import Langlands.Analysis.CanonicalScalarAnalyticityFromWeighted
import Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransport

/-! # Reduction of generic scalar regularity to weighted estimates -/

noncomputable section
universe v
set_option autoImplicit false

namespace Langlands.Analysis

/-- Generic scalar regularity, with the weighted PDE estimate as an explicit premise. -/
theorem scalarEllipticAnalyticity_of_weightedFactorialBounds
    (hestimate : ∀ d r : ℕ, CanonicalScalarWeightedFactorialBoundsStatement d r)
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ) :
    ScalarEllipticAnalyticityStatement E d r :=
  euclideanScalarEllipticAnalyticityTransport E d r
    (canonicalEuclideanScalarEllipticAnalyticity_of_all_weightedFactorialBounds
      hestimate d r)

example :
    (∀ d r : ℕ, CanonicalScalarWeightedFactorialBoundsStatement d r) →
    ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ),
      ScalarEllipticAnalyticityStatement E d r :=
  @scalarEllipticAnalyticity_of_weightedFactorialBounds

end Langlands.Analysis
