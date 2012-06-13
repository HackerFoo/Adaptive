{-  
    This file is part of Adaptive.

    Adaptive is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Adaptive is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with Adaptive.  If not, see <http://www.gnu.org/licenses/>.
-}

{-# LANGUAGE FlexibleInstances, BangPatterns, UnboxedTuples #-}
{-# OPTIONS_GHC -fno-excess-precision -fno-spec-constr #-}
-- {-# OPTIONS_GHC -fglasgow-exts -fno-excess-precision -fno-spec-constr #-}
-- use SSE to avoid the excess precision of the 387 FPU
-- {-# OPTIONS_GHC -fvia-C -optc-O -optc-ffast-math -optc-mfpmath=sse -optc-msse #-}
-- {-# OPTIONS_GHC -fllvm -optlc-mattr=+sse4a -optlc--disable-excess-fp-precision #-}

-- | Based on Adaptive Precision Floating-Point Arithmetic and Fast Robust Geometric Predicates, Jonathan Richard Shewchuk, 1997
module Data.Adaptive (Adaptive(..), fromFloatingPoint, approx, approx', approxFast, splitter, epsilon) where

import Data.List
import Data.Bits
import Data.Ratio

type FloatT = Double

--mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy _ xs [] = xs
mergeBy _ [] ys = ys
mergeBy cmp (x:xs) (y:ys) = case cmp x y of
                              GT -> y : mergeBy cmp (x:xs) ys
                              _ -> x : mergeBy cmp xs (y:ys)

newtype Adaptive a = Adaptive [a]

instance (Show a, RealFloat a) => Show (Adaptive a) where
  showsPrec n x = showParen (n > 6 && x < 0) $ showsPrec 0 (approx x) . ('~':)

------------------------- approximate instances -------------------------

liftAdaptive1 f = fromFloatingPoint . f . approxFast
liftAdaptive2 f x y = fromFloatingPoint $ approxFast x `f` approxFast y

instance (RealFloat a, Real a) => Real (Adaptive a) where
  toRational = toRational . approxFast

instance (RealFloat a, Floating a) => Floating (Adaptive a) where
  pi = fromFloatingPoint pi
  exp = liftAdaptive1 exp
  sqrt = sqrtA
  log = liftAdaptive1 log
  (**) = liftAdaptive2 (**)
  logBase = liftAdaptive2 logBase
  sin = liftAdaptive1 sin
  tan = liftAdaptive1 tan
  cos = liftAdaptive1 cos
  asin = liftAdaptive1 asin
  atan = liftAdaptive1 atan
  acos = liftAdaptive1 acos
  sinh = liftAdaptive1 sinh
  tanh = liftAdaptive1 tanh
  cosh = liftAdaptive1 cosh
  asinh = liftAdaptive1 asinh
  atanh = liftAdaptive1 atanh
  acosh = liftAdaptive1 acosh

instance (RealFloat a) => RealFloat (Adaptive a) where
  floatRadix = floatRadix . approxFast
  floatDigits = floatDigits . approxFast
  floatRange = floatRange . approxFast
  decodeFloat = decodeFloat . approxFast
  encodeFloat s r = fromFloatingPoint (encodeFloat s r)
  exponent = exponent . approxFast
  significand = liftAdaptive1 significand
  scaleFloat x = liftAdaptive1 (scaleFloat x)
  isNaN = isNaN . approxFast
  isInfinite = isInfinite . approxFast
  isDenormalized = isDenormalized . approxFast
  isNegativeZero = isNegativeZero . approxFast
  isIEEE = isIEEE . approxFast
  atan2 = liftAdaptive2 atan2

instance (RealFloat a, RealFrac a) => RealFrac (Adaptive a) where
  properFraction x = (y, fromFloatingPoint x')
    where (y, x') = properFraction (approxFast x)

-------------------------------------------------------------------------

instance (Num a, RealFloat a) => Eq (Adaptive a) where
  {-# SPECIALIZE instance Eq (Adaptive FloatT) #-}
  a == b | null x = True
         | otherwise = False
    where Adaptive x = a - b

instance (Num a, RealFloat a) => Ord (Adaptive a) where
  {-# SPECIALIZE instance Ord (Adaptive FloatT) #-}
  compare a b | null x = EQ
              | head x > 0 = GT
              | otherwise = LT
    where Adaptive x = a - b

instance (Num a, RealFloat a) => Num (Adaptive a) where
  {-# SPECIALIZE instance Num (Adaptive FloatT) #-}
  Adaptive x + Adaptive y = Adaptive . compress $ fastExpSum x y
  Adaptive x - Adaptive y = Adaptive x + Adaptive (map negate y)
  Adaptive x * Adaptive y = Adaptive $ expProd x y
  negate (Adaptive x) = Adaptive (map negate x)
  abs (Adaptive []) = Adaptive []
  abs (Adaptive x) | head x < 0 = Adaptive (map negate x)
                   | otherwise = Adaptive x
  signum (Adaptive []) = Adaptive []
  signum (Adaptive (x:_)) = Adaptive [signum x]
  fromInteger 0 = Adaptive []
  fromInteger x = Adaptive [fromInteger x]

instance (RealFloat a, Fractional a) => Fractional (Adaptive a) where
  {-# SPECIALIZE instance Fractional (Adaptive FloatT) #-}
  fromRational r = fromIntegral (numerator r) / fromIntegral (denominator r)
  a / b = Adaptive $ a `divA` b

{-# SPECIALIZE divA :: Adaptive FloatT -> Adaptive FloatT -> [FloatT] #-}
divA x y | d == 0 = []
         | e == 0 || abs e >= abs x = [d]
         | otherwise = d : divA e y
  where d = approxFast x / approxFast y
        e = x - fromFloatingPoint d * y

-- | Use Babylonian method to calculate corrections to built in sqrt
{-# SPECIALIZE sqrtA :: Adaptive FloatT -> Adaptive FloatT #-}
sqrtA x = r + bab r
  where r = liftAdaptive1 sqrt x
        bab e | c == 0 = 0
              | otherwise = c + bab (e + c)
          where c = (x / e - e) / 2

{-# SPECIALIZE epsilon :: FloatT #-}
epsilon :: (RealFloat a) => a
epsilon = x
  where x = scaleFloat (- floatDigits x) 1

{-# SPECIALIZE splitter :: FloatT #-}
splitter :: (RealFloat a) => a
splitter = s
  where s = scaleFloat ((floatDigits s + 1) `shiftR` 1) 1 + 1

-- {-# INLINE fromFloatingPoint #-}
{-# SPECIALIZE fromFloatingPoint :: FloatT -> Adaptive FloatT #-}
fromFloatingPoint :: (RealFloat a) => a -> Adaptive a
fromFloatingPoint 0 = Adaptive []
fromFloatingPoint x = Adaptive [x]

{-# INLINE approx #-}
-- {-# SPECIALIZE approx :: Adaptive FloatT -> FloatT #-}
approx :: (RealFloat a, Ord a) => Adaptive a -> a
approx (Adaptive []) = 0
approx (Adaptive (x:xs)) = foldr (+) x . takeWhile ((> x*epsilon).abs) $ xs

{-# INLINE approx' #-}
-- {-# SPECIALIZE approx' :: Adaptive FloatT -> FloatT #-}
approx' :: (Real a, RealFloat b) => Adaptive a -> b
approx' (Adaptive []) = 0
approx' (Adaptive (x:xs)) = foldr (+) x' .
                            takeWhile ((> x' * epsilon) . abs) .
                            map realToFrac $ xs
  where x' = realToFrac x

-- {-# INLINE approxFast #-}
{-# SPECIALIZE approxFast :: Adaptive FloatT -> FloatT #-}
approxFast :: (Num a) => Adaptive a -> a
approxFast (Adaptive []) = 0
approxFast (Adaptive (x:_)) = x

-- |a| >= [b]
{-# INLINE fastTwoSum #-}
--{-# SPECIALIZE fastTwoSum :: FloatT -> FloatT -> (# FloatT, FloatT #) #-}
fastTwoSum :: (Num a) => a -> a -> (# a, a #)
fastTwoSum a b = (# x, y #)
  where x = a + b
        b' = x - a
        y = b - b'

{-# INLINE twoSum #-}
--{-# SPECIALIZE twoSum :: FloatT -> FloatT -> (# FloatT, FloatT #) #-}
twoSum :: (Num a) => a -> a -> (# a, a #)
twoSum !a !b = (# x, y #)
  where !x = a + b
        !b' = x - a
        !a' = x - b'
        !br = b - b'
        !ar = a - a'
        !y = ar + br

{-
{-# INLINE twoSum' #-}
--{-# SPECIALIZE twoSum' :: FloatT -> FloatT -> (FloatT, FloatT) #-}
twoSum' :: (Num a) => a -> a -> (a, a)
twoSum' a b = (x, y)
  where x = a + b
        b' = x - a
        a' = x - b'
        br = b - b'
        ar = a - a'
        y = ar + br

--{-# SPECIALIZE growExp :: FloatT -> [FloatT] -> [FloatT] #-}
growExp :: (Num a) => a -> [a] -> [a]
growExp b es = filter (/= 0) . uncurry (:) . mapAccumR twoSum' b $ es

--{-# SPECIALIZE expSum :: [FloatT] -> [FloatT] -> [FloatT] #-}
expSum :: (Num a) => [a] -> [a] -> [a]
expSum = foldr growExp
-}

{-# SPECIALIZE fastExpSum :: [FloatT] -> [FloatT] -> [FloatT] #-}
fastExpSum :: (RealFloat a) => [a] -> [a] -> [a]
fastExpSum [] x = x
fastExpSum x [] = x
fastExpSum e f = filter (/= 0) (q:hs)
  where g = mergeBy cmp e f
        cmp x y = compare (exponent y) (exponent x)
        (# q, hs #) = mapAccumR1 twoSum g

--mapAccumR1 :: (t -> t -> (# t, a #)) -> [t] -> (# t, [a] #)
mapAccumR1 f [x] = (# x, [] #)
mapAccumR1 f (x:xs) = (# a', y:xs' #)
  where (# a, xs' #) = mapAccumR1 f xs
        (# a', y #) = f a x

--{-# INLINE split #-}
--{-# SPECIALIZE split :: FloatT -> (# FloatT, FloatT #) #-}
--split :: (RealFloat a) => a -> (# a, a #)
split !a = (# ah, al #)
  where !c = splitter * a
        !ab = c - a
        !ah = c - ab
        !al = a - ah

--{-# INLINE twoProd #-}
--{-# SPECIALIZE twoProd :: FloatT -> FloatT -> (# FloatT, FloatT #) #-}
--twoProd :: (RealFloat a) => a -> a -> (# a, a #)
twoProd !a !b = (# x, y #)
  where !x = a * b
        (# !ah, !al #) = split a
        (# !bh, !bl #) = split b
        !err = x - ah * bh - al * bh - ah * bl
        !y = al * bl - err

--{-# INLINE scaleExp #-}
--{-# SPECIALIZE scaleExp :: FloatT -> [FloatT] -> [FloatT] #-}
--scaleExp :: (RealFloat a) => a -> [a] -> [a]
scaleExp _ [] = []
scaleExp b es = filter (/= 0) . (uncurry (:)) . foldr f (q0, [h0]) . init $ es
  where (# q0, h0 #) = twoProd (last es) b
        f e (q, h) = (q'', h2 : h1 : h)
          where (# th, tl #) = twoProd e b
                (# q', h1 #) = twoSum q tl
                (# q'', h2 #) = fastTwoSum th q'

--{-# INLINE expProd #-}
--{-# SPECIALIZE expProd :: [FloatT] -> [FloatT] -> [FloatT] #-}
--expProd :: (RealFloat a) => [a] -> [a] -> [a]
expProd [] _ = []
expProd _ [] = []
expProd x [y] = scaleExp y x
expProd [x] y = scaleExp x y
expProd (x:xs) ys = foldl' f (scaleExp x ys) xs
  where f h e = fastExpSum h . scaleExp e $ ys

--{-# SPECIALIZE compress :: [FloatT] -> [FloatT] #-}
--compress :: (Num a) => [a] -> [a]
compress e = comp up . comp down $ e
  where comp _ [] = []
        comp _ [x] = [x]
        comp f (x:xs) = uncurry (:) . foldl' f (x, []) $ xs
        down (q, h) e | ql /= 0 = (ql, qu:h)
                      | otherwise = (qu, h)
          where (# qu, ql #) = fastTwoSum q e
        up (q, h) e | ql /= 0 = (qu, ql:h) -- error on pg. 28, line 14: Q should be q
                    | otherwise = (qu, h)
          where (# qu, ql #) = fastTwoSum e q
