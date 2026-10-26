import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Representation.Exponents.Chambers

/-! # Weighted scalar-root parameters and strict prefix cones

An internal finite-coordinate comparison. This module states the comparison
without proving it.
-/

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeRegularComparison

/-- The existing scalar-root parameter is equivalent to the open root cone
in size-weighted coordinates within each original block. -/
def PositiveRootParameterConeStatement : Prop :=
  ∀ (n : ℕ) (D : BlockShape n) (R : BlockRefinement D)
    (v : Fin (D.flatten R).length → ℝ),
    IsPositiveRootParameter D R v ↔
      ∀ i : Fin D.length,
        IsPositiveRootCone (fun k : Fin (R i).length =>
          ((R i).size k : ℝ) * v (D.flattenBlockEquiv R ⟨i, k⟩))

end Langlands.Exponents
