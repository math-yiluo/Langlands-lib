import Langlands.AbelianScheme.Tate.AbelianPrimeAdic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Rank of the actual prime-adic Tate module at a geometric point -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate.PrimeAdic

/-- At an algebraically closed point, an abelian scheme of relative dimension
`g` has integral Tate module free of rank `2 * g` and rational Tate module of
dimension `2 * g`, for a prime invertible on the base. This is a proof target. -/
def GeometricPrimeAdicRankStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (g : ℕ),
    A.HasRelativeDimension g →
      ∀ (p : ℕ) [Fact p.Prime],
        IsUnit (p : Γ(S, ⊤)) →
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (s : Spec (CommRingCat.of Ω) ⟶ S),
            Nonempty ((Fin (2 * g) → ℤ_[p]) ≃ₗ[ℤ_[p]] IntegralAt A p s) ∧
              FiniteDimensional ℚ_[p] (RationalAt A p s) ∧
                Module.finrank ℚ_[p] (RationalAt A p s) = 2 * g

end Langlands.AbelianScheme.Tate.PrimeAdic
