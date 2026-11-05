import Langlands.Representation.Plancherel.RationalModerateGrowthStatement

/-! # Power comparison for actual rational-point matrix norms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open GroupScheme MatrixRepresentation

universe u

/-- The norm of any algebraic matrix representation is power-bounded by the
norm of a supplied closed embedding of the same group scheme. -/
def RationalMatrixNormComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (n m : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype m] [DecidableEq m] [Nonempty m]
    (ρ : MatrixRepresentation G n), IsClosedSubgroup ρ →
    ∀ τ : MatrixRepresentation G m,
      ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : rationalPoints G,
        rationalMatrixNorm F τ g ≤ c * rationalMatrixNorm F ρ g ^ d

end Langlands.Plancherel
