import Langlands.Analysis.ScalarEllipticAnalyticityDegenerate
import Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransportStatement

/-! # Elementary boundary cases of canonical Euclidean scalar regularity -/

noncomputable section
open scoped ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- The canonical Euclidean assertion holds in dimension zero, at every order. -/
theorem canonicalEuclideanScalarEllipticAnalyticity_dimension_zero (r : ℕ) :
    CanonicalEuclideanScalarEllipticAnalyticityStatement 0 r := by
  intro D S F _ hS hcoeff hell hF heqn
  exact scalarEllipticAnalyticity_dimension_zero (EuclideanSpace ℝ (Fin 0)) r
    D S F hS hcoeff hell hF heqn

/-- The canonical Euclidean assertion holds at order zero, in every dimension. -/
theorem canonicalEuclideanScalarEllipticAnalyticity_order_zero (d : ℕ) :
    CanonicalEuclideanScalarEllipticAnalyticityStatement d 0 := by
  intro D S F _ hS hcoeff hell hF heqn
  exact scalarEllipticAnalyticity_order_zero (EuclideanSpace ℝ (Fin d)) d
    D S F hS hcoeff hell hF heqn

/-- It suffices to prove canonical Euclidean scalar regularity in positive dimensions
and positive orders. -/
theorem canonicalEuclideanScalarEllipticAnalyticity_of_positive
    (hpositive : ∀ d r : ℕ, 0 < d → 0 < r →
      CanonicalEuclideanScalarEllipticAnalyticityStatement d r)
    (d r : ℕ) : CanonicalEuclideanScalarEllipticAnalyticityStatement d r := by
  cases d with
  | zero => exact canonicalEuclideanScalarEllipticAnalyticity_dimension_zero r
  | succ d =>
    cases r with
    | zero => exact canonicalEuclideanScalarEllipticAnalyticity_order_zero (d + 1)
    | succ r => exact hpositive (d + 1) (r + 1) (Nat.succ_pos d) (Nat.succ_pos r)

end Langlands.Analysis
