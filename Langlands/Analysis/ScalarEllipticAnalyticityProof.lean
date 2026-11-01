import Langlands.Analysis.ScalarEllipticAnalyticityReduction
import Langlands.Analysis.CanonicalScalarWeightedFactorialBoundsProof

/-! # Scalar analytic elliptic regularity -/

noncomputable section
universe v
set_option autoImplicit false

namespace Langlands.Analysis

/-- Analytic elliptic regularity on the original real normed space, with no
restriction on its finite coordinate dimension or the operator order. -/
theorem scalarEllipticAnalyticity
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ) :
    ScalarEllipticAnalyticityStatement E d r :=
  scalarEllipticAnalyticity_of_weightedFactorialBounds
    (fun _ _ => canonicalScalarWeightedFactorialBounds) E d r

example :
    ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ),
      ScalarEllipticAnalyticityStatement E d r :=
  @scalarEllipticAnalyticity

end Langlands.Analysis
