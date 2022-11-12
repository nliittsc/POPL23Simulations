
module Utils where


data multi {X : Set} (R : X → X → Set) : X → X → Set where
  refl : ∀{x} → multi R x x
  iter : ∀{x y z} → R x y → multi R y z → multi R x z
