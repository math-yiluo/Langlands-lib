import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # An L2 test from polynomial-geometric lattice cell bounds -/

namespace Langlands

open MeasureTheory
open scoped BigOperators ENNReal

/-- Polynomial coefficient bounds and geometric cell-volume bounds give `L²`
when their coordinatewise squared-coefficient/volume weights are below one.
The finite coordinate type may be empty; cells need not be measurable or disjoint. -/
def FiniteLatticeCellL2Statement.{uX, uI} : Prop :=
  ∀ (X : Type uX) [MeasurableSpace X] (I : Type uI) [Fintype I]
    (μ : Measure X) (f : X → ℝ),
    AEStronglyMeasurable f μ →
    ∀ (cell : (I → ℕ) → Set X), (⋃ n, cell n) = Set.univ →
    ∀ (C D : ℝ), 0 ≤ C → 0 ≤ D →
    ∀ (a w : I → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ w i) →
      (∀ i, (a i) ^ 2 * w i < 1) →
    ∀ (d : ℕ),
      (∀ n x, x ∈ cell n →
        ‖f x‖ ≤ C * (1 + ∑ i, (n i : ℝ)) ^ d * ∏ i, (a i) ^ n i) →
      (∀ n, μ (cell n) ≤ ENNReal.ofReal (D * ∏ i, (w i) ^ n i)) →
      MemLp f 2 μ

end Langlands
