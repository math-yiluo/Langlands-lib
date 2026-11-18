import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Geometric splitting of finite étale covers of affine space -/

universe u

namespace Langlands.Algebra

/-- Finite étale covers of affine space over an algebraically closed field of
characteristic zero are finite disjoint unions of copies of that affine space. -/
def AffineSpaceFiniteEtaleGeometricSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n : ℕ)
    (A : Type u) [CommRing A] [Algebra (MvPolynomial (Fin n) k) A],
    Algebra.Etale (MvPolynomial (Fin n) k) A →
    Module.Finite (MvPolynomial (Fin n) k) A →
      ∃ m : ℕ, Nonempty
        (A ≃ₐ[MvPolynomial (Fin n) k] (Fin m → MvPolynomial (Fin n) k))

end Langlands.Algebra
