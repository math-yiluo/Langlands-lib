import Langlands.Analysis.ScalarEllipticAnalyticityStatement
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The canonical Euclidean scalar regularity assertion and its coordinate reduction -/

noncomputable section
universe v
open scoped ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- Scalar analytic elliptic regularity on real Euclidean space with its canonical basis. -/
def CanonicalEuclideanScalarEllipticAnalyticityStatement (d r : ℕ) : Prop :=
  ∀ (D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r)
    (S : Set (EuclideanSpace ℝ (Fin d))) (F : EuclideanSpace ℝ (Fin d) → ℂ),
    D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis →
    IsOpen S → D.AnalyticCoefficientsOn S → D.IsEllipticOn S →
    ContDiffOn ℝ ∞ F S → (∀ x ∈ S, D.action F x = 0) →
    AnalyticOnNhd ℝ F S

/-- Canonical Euclidean regularity suffices for the unchanged generic scalar assertion. -/
def EuclideanScalarEllipticAnalyticityTransportStatement
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ) : Prop :=
  CanonicalEuclideanScalarEllipticAnalyticityStatement d r →
    ScalarEllipticAnalyticityStatement E d r

end Langlands.Analysis
