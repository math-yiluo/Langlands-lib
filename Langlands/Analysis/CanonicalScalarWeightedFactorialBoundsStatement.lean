import Langlands.Analysis.CoordinateScalarDifferentialOperator
import Langlands.Analysis.LocalEllipticCutoffEstimate

/-! # Actual weighted factorial derivative bounds for a scalar elliptic equation -/

noncomputable section
open scoped ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- On one shrinkable ball, every actual complete ordered derivative tensor of
an elliptic analytic-coefficient solution satisfies a common factorial bound.
This statement is restricted to positive dimension and positive operator order. -/
def CanonicalScalarWeightedFactorialBoundsStatement (d r : ℕ) : Prop :=
  0 < d → 0 < r →
  ∀ D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r,
    D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis →
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsOpen S →
      D.AnalyticCoefficientsOn S → D.IsEllipticOn S →
      ∀ u : EuclideanSpace ℝ (Fin d) → ℂ, ContDiffOn ℝ ∞ u S →
        (∀ x ∈ S, D.action u x = 0) →
        ∀ x₀ ∈ S, ∀ R₀ : ℝ, 0 < R₀ →
          ∃ R C A : ℝ, 0 < R ∧ R ≤ R₀ ∧ Metric.closedBall x₀ R ⊆ S ∧
            0 < C ∧ 0 < A ∧
            ∀ k : ℕ, ballWeightedSeminorm (derivWordNorm k u) x₀ R k ≤
              ENNReal.ofReal (C * A ^ k * (k.factorial : ℝ))

end Langlands.Analysis
