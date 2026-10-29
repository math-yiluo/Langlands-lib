import Langlands.Analysis.CoordinateScalarDifferentialOperator
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! # Interior analytic regularity for coordinate scalar elliptic operators -/

noncomputable section
universe v
open scoped ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- A smooth homogeneous solution of an actual scalar elliptic equation with analytic
coefficients is real analytic throughout its open domain, in the original norm. -/
def ScalarEllipticAnalyticityStatement
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ) : Prop :=
  ∀ (D : CoordinateScalarOperator E d r) (S : Set E) (F : E → ℂ),
    IsOpen S → D.AnalyticCoefficientsOn S → D.IsEllipticOn S →
    ContDiffOn ℝ ∞ F S → (∀ x ∈ S, D.action F x = 0) →
    AnalyticOnNhd ℝ F S

end Langlands.Analysis
