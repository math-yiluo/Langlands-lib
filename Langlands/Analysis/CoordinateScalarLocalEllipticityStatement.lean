import Langlands.Analysis.CoordinateScalarDifferentialOperator

/-! # A local uniform lower bound for a scalar elliptic symbol -/

noncomputable section
universe v
set_option autoImplicit false

namespace Langlands.Analysis

/-- Pointwise ellipticity and continuity of the actual top coefficients imply a
homogeneous lower bound on an open neighborhood, for positive differential order. -/
def CoordinateScalarLocalEllipticityStatement
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ) : Prop :=
  0 < r →
    ∀ (D : CoordinateScalarOperator E d r) (x₀ : E),
      (∀ w : Fin r → Fin d, ContinuousAt (D.coefficient (Fin.last r) w) x₀) →
      (∀ ξ : E →L[ℝ] ℝ, ξ ≠ 0 → D.principalSymbol x₀ ξ ≠ 0) →
      ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ D.IsUniformlyEllipticOn U

end Langlands.Analysis
