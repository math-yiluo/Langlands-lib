import Mathlib

/-! # Real analyticity from weighted factorial L² bounds -/

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- Factorial bounds on the radius-weighted L² norms of all ordered derivative
tensors imply real analyticity at the centre of the ball. -/
def WeightedL2FactorialAnalyticityStatement (d : ℕ) : Prop :=
  ∀ (F : EuclideanSpace ℝ (Fin d) → ℂ) (x₀ : EuclideanSpace ℝ (Fin d))
    (R C A : ℝ), 0 < R → ContDiffOn ℝ ∞ F (ball x₀ R) →
    (∀ k : ℕ,
      (⨆ ρ ∈ Ico (R / 2) R,
        ENNReal.ofReal ((R - ρ) ^ k) *
          eLpNorm
            (fun y => Real.sqrt (∑ w : Fin k → Fin d,
              ‖iteratedFDeriv ℝ k F y
                (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j))‖ ^ 2))
            2 (volume.restrict (ball x₀ ρ))) ≤
        ENNReal.ofReal (C * A ^ k * Nat.factorial k)) →
    AnalyticAt ℝ F x₀

end Langlands.Analysis
