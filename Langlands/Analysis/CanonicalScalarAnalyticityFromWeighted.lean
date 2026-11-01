import Langlands.Analysis.CanonicalScalarWeightedFactorialBoundsStatement
import Langlands.Analysis.WeightedL2FactorialAnalyticity
import Langlands.Analysis.EuclideanScalarEllipticAnalyticityDegenerate

/-! # Canonical scalar regularity from the weighted factorial estimate -/

noncomputable section
open Metric Set
open scoped ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- Conditional connection from the actual weighted PDE estimate to
canonical scalar analytic regularity in positive dimension and order. -/
theorem canonicalEuclideanScalarEllipticAnalyticity_of_weightedFactorialBounds
    (d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hestimate : CanonicalScalarWeightedFactorialBoundsStatement d r) :
    CanonicalEuclideanScalarEllipticAnalyticityStatement d r := by
  intro D S F hbasis hS hcoeff hell hF heqn x₀ hx₀
  obtain ⟨R, C, A, hR, _hRle, hclosed, _hC, _hA, hweighted⟩ :=
    hestimate hd hr D hbasis S hS hcoeff hell F hF heqn x₀ hx₀ 1 zero_lt_one
  exact weightedL2FactorialAnalyticity d F x₀ R C A hR
    (hF.mono (ball_subset_closedBall.trans hclosed)) hweighted

/-- The zero cases remove every positivity restriction from the regularity
conclusion; the weighted estimate remains an explicit premise. -/
theorem canonicalEuclideanScalarEllipticAnalyticity_of_all_weightedFactorialBounds
    (hestimate : ∀ d r : ℕ, CanonicalScalarWeightedFactorialBoundsStatement d r)
    (d r : ℕ) : CanonicalEuclideanScalarEllipticAnalyticityStatement d r :=
  canonicalEuclideanScalarEllipticAnalyticity_of_positive
    (fun d r hd hr =>
      canonicalEuclideanScalarEllipticAnalyticity_of_weightedFactorialBounds
        d r hd hr (hestimate d r)) d r

end Langlands.Analysis
