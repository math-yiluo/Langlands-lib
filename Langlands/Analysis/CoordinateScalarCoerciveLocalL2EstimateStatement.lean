import Langlands.Analysis.CoordinateScalarDifferentialOperator
import Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement

/-! # A local coercive scalar L² estimate -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- After shrinking a coefficient neighborhood, the full action and the function
control the top ordered derivative tensor with one uniform constant. -/
def CoordinateScalarCoerciveLocalL2EstimateStatement (d r : ℕ) : Prop :=
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  ∀ (D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r),
    D.basis = e.toBasis →
    ∀ (S : Set (EuclideanSpace ℝ (Fin d))), IsOpen S →
      (∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
        ContinuousOn (D.coefficient k w) S) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)), x₀ ∈ S →
        ∀ (c : ℝ), 0 < c →
          (∀ ξ : EuclideanSpace ℝ (Fin d),
            c * ‖ξ‖ ^ r ≤ ‖∑ w : Fin r → Fin d,
              D.coefficient (Fin.last r) w x₀ * ∏ j : Fin r, (ξ (w j) : ℂ)‖) →
          ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ Metric.closedBall x₀ R ⊆ S ∧
            ∀ (F : EuclideanSpace ℝ (Fin d) → ℂ),
              ContDiff ℝ ∞ F → tsupport F ⊆ Metric.closedBall x₀ R →
              eLpNorm
                  (fun x => Real.sqrt (∑ w : Fin r → Fin d,
                    ‖iteratedFDeriv ℝ r F x (fun j => e (w j))‖ ^ 2))
                  2 volume ≤
                ENNReal.ofReal C * (eLpNorm (D.action F) 2 volume + eLpNorm F 2 volume)

end Langlands.Analysis
