import Langlands.Analysis.ScalarEllipticAnalyticityStatement

/-! # Scalar elliptic analytic regularity in zero dimension or zero order -/

noncomputable section
universe v
set_option autoImplicit false

namespace Langlands.Analysis

/-- The unchanged generic scalar assertion in every case with dimension or order zero. -/
def ScalarEllipticAnalyticityDegenerateStatement
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  (∀ r : ℕ, ScalarEllipticAnalyticityStatement E 0 r) ∧
    (∀ d : ℕ, ScalarEllipticAnalyticityStatement E d 0)

end Langlands.Analysis
