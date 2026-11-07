import Langlands.Representation.Unitary.IntegratedActionLeftTranslationStatement

noncomputable section

universe uG uE

namespace Langlands.Analysis

open MeasureTheory

/-- Commute the action with the integral and substitute a left translation. -/
theorem integratedActionLeftTranslation :
    IntegratedActionLeftTranslationStatement.{uG, uE} := by
  intro G _ _ _ E _ _ _ μ _ π hπnorm hπmeas f hf x p
  constructor
  · exact isometricActionIntegrand_integrable μ π hπnorm hπmeas
      (fun y => f (p⁻¹ * y)) (hf.comp_mul_left p⁻¹) x
  · rw [integratedIsometricAction_apply,
      ← (π p).integral_comp_comm
        (isometricActionIntegrand_integrable μ π hπnorm hπmeas f hf x)]
    calc
      (∫ g, π p (f g • π g x) ∂μ) =
          ∫ g, f (p⁻¹ * (p * g)) • π (p * g) x ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun g => by
              simp only [inv_mul_cancel_left, map_smul, map_mul,
                mul_apply_eq_comp]
      _ = ∫ y, f (p⁻¹ * y) • π y x ∂μ :=
        integral_mul_left_eq_self (fun y => f (p⁻¹ * y) • π y x) p

end Langlands.Analysis
