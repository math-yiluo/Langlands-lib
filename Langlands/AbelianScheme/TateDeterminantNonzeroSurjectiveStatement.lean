import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.Tate.RationalPrimeHom
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant

/-! # An endomorphism with invertible rational Tate map is surjective -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Let `α` be an endomorphism of an abelian scheme `A` over an algebraically closed field
`k` of characteristic zero, and let `p` be a prime. If the determinant of the actual rational
`p`-adic Tate map of `α` is nonzero, then the underlying scheme morphism of `α` is
surjective. This proposition is a statement target, not a proof. -/
def TateDeterminantNonzeroSurjectiveStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] (α : A ⟶ A),
      LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α) ≠ 0 →
        Surjective (hom α)

end Langlands.AbelianScheme
