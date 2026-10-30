import Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement

/-! # Absorbing a small perturbation of an elliptic principal coefficient array -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- A principal coefficient array whose total difference from a constant elliptic
array is at most half the symbol constant on the support obeys an L² estimate. -/
def PrincipalCoefficientPerturbationL2Statement (d r : ℕ) : Prop :=
  let e : Fin d → EuclideanSpace ℝ (Fin d) := EuclideanSpace.basisFun (Fin d) ℝ
  ∀ (a₀ : (Fin r → Fin d) → ℂ) (c : ℝ), 0 < c →
    (∀ ξ : EuclideanSpace ℝ (Fin d),
      c * ‖ξ‖ ^ r ≤ ‖∑ w : Fin r → Fin d, a₀ w * ∏ j : Fin r, (ξ (w j) : ℂ)‖) →
    ∀ (a : (Fin r → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
      (F : EuclideanSpace ℝ (Fin d) → ℂ),
      ContDiff ℝ ∞ F → HasCompactSupport F →
      (∀ x ∈ tsupport F, ∑ w : Fin r → Fin d, ‖a₀ w - a w x‖ ≤ c / 2) →
      eLpNorm
          (fun x => Real.sqrt
            (∑ w : Fin r → Fin d, ‖iteratedFDeriv ℝ r F x (fun j => e (w j))‖ ^ 2))
          2 volume ≤
        ENNReal.ofReal (2 * c⁻¹) *
          eLpNorm
            (fun x => ∑ w : Fin r → Fin d,
              a w x * iteratedFDeriv ℝ r F x (fun j => e (w j)))
            2 volume

end Langlands.Analysis
