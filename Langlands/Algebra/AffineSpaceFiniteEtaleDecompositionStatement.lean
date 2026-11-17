import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # A polynomial product decomposition for finite étale covers of affine space -/

universe u

namespace Langlands.Algebra

/-- A ring-theoretic consequence of the classification of finite étale covers of affine
space in characteristic zero: the covering ring is a finite product of polynomial rings
over fields. The isomorphism asserted here need not preserve the base algebra structure. -/
def AffineSpaceFiniteEtalePolynomialProductStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (A : Type u) [CommRing A]
    [Algebra (MvPolynomial (Fin n) k) A],
    Algebra.Etale (MvPolynomial (Fin n) k) A → Module.Finite (MvPolynomial (Fin n) k) A →
      ∃ (ι : Type u) (_ : Finite ι) (K : ι → Type u) (_ : ∀ i, Field (K i)),
        Nonempty (A ≃+* ∀ i, MvPolynomial (Fin n) (K i))

end Langlands.Algebra
