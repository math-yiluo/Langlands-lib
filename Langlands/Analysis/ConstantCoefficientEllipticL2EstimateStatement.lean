import Langlands.Analysis.CoordinateScalarDifferentialOperator
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The scalar constant-coefficient elliptic L² estimate -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- A homogeneous scalar symbol lower bound controls the L² norm of the complete
ordered top-derivative tensor of a compactly supported smooth function. -/
def ConstantCoefficientEllipticL2EstimateStatement (d r : ℕ) : Prop :=
  let e : Fin d → EuclideanSpace ℝ (Fin d) := EuclideanSpace.basisFun (Fin d) ℝ
  ∀ (a : (Fin r → Fin d) → ℂ) (c : ℝ), 0 < c →
    (∀ ξ : EuclideanSpace ℝ (Fin d),
      c * ‖ξ‖ ^ r ≤ ‖∑ w : Fin r → Fin d, a w * ∏ j : Fin r, (ξ (w j) : ℂ)‖) →
    ∀ F : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      eLpNorm
          (fun x => Real.sqrt
            (∑ w : Fin r → Fin d, ‖iteratedFDeriv ℝ r F x (fun j => e (w j))‖ ^ 2))
          2 volume ≤
        ENNReal.ofReal c⁻¹ *
          eLpNorm
            (fun x => ∑ w : Fin r → Fin d,
              a w * iteratedFDeriv ℝ r F x (fun j => e (w j)))
            2 volume

end Langlands.Analysis
