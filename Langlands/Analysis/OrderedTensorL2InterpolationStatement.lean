import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Interpolation between complete ordered derivative tensors in L² -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- An arbitrary positive scale interpolates a lower ordered derivative tensor
between the highest ordered tensor and the function itself. -/
def OrderedTensorL2InterpolationStatement (d r : ℕ) : Prop :=
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  ∀ (k : ℕ), k ≤ r → ∀ (ε : ℝ), 0 < ε →
    ∀ (F : EuclideanSpace ℝ (Fin d) → ℂ),
      ContDiff ℝ ∞ F → HasCompactSupport F →
      eLpNorm
          (fun x => Real.sqrt (∑ w : Fin k → Fin d,
            ‖iteratedFDeriv ℝ k F x (fun j => e (w j))‖ ^ 2))
          2 volume ≤
        ENNReal.ofReal (ε ^ (r - k)) *
            eLpNorm
              (fun x => Real.sqrt (∑ w : Fin r → Fin d,
                ‖iteratedFDeriv ℝ r F x (fun j => e (w j))‖ ^ 2))
              2 volume +
          ENNReal.ofReal (ε⁻¹ ^ k) * eLpNorm F 2 volume

end Langlands.Analysis
