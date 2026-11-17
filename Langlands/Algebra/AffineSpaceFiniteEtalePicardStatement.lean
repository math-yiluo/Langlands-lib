import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Statement: finite étale covers of affine space in characteristic zero have trivial
Picard group -/

universe u

namespace Langlands.Algebra

/-- **Finite étale covers of `𝔸ⁿ_k` have trivial Picard group when `char k = 0`.** For every
field `k : Type u` of characteristic zero, every `n : ℕ` and every commutative ring
`A : Type u` that is a finite étale `k[x₁, …, xₙ]`-algebra, `Subsingleton (CommRing.Pic A)`:
every invertible `A`-module is free. -/
def AffineSpaceFiniteEtalePicardTrivialStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (A : Type u) [CommRing A]
    [Algebra (MvPolynomial (Fin n) k) A],
    Algebra.Etale (MvPolynomial (Fin n) k) A → Module.Finite (MvPolynomial (Fin n) k) A →
      Subsingleton (CommRing.Pic A)

end Langlands.Algebra
