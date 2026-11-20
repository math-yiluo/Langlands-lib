import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Logarithmic radius for complex multiplicative diagonal integration -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped NNReal ENNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

set_option autoImplicit false

private def inverseSquareDensity (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (‖z‖ ^ 2)⁻¹

private theorem measurable_inverseSquareDensity : Measurable inverseSquareDensity :=
  (continuous_norm.measurable.pow_const 2).inv.ennreal_ofReal

/-- Multiplicative complex Lebesgue measure represented on `ℂ` with density `‖z‖⁻²` and
zero mass at the origin. -/
def multiplicativeComplexLebesgue : Measure ℂ :=
  (volume : Measure ℂ).withDensity inverseSquareDensity

private theorem measurable_log_norm : Measurable (fun z : ℂ => Real.log ‖z‖) :=
  Real.measurable_log.comp continuous_norm.measurable

private theorem lintegral_inverse_mul_log (F : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * F (Real.log r)) = ∫⁻ y, F y := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn
    (fun r => ENNReal.ofReal r⁻¹ * F (Real.log r))
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  apply lintegral_congr
  intro y
  simp only [abs_of_pos (Real.exp_pos y), Real.log_exp, ← mul_assoc]
  rw [← ENNReal.ofReal_mul (Real.exp_pos y).le, mul_inv_cancel₀ (Real.exp_ne_zero y),
    ENNReal.ofReal_one, one_mul]

/-- The logarithmic radius pushes complex multiplicative Lebesgue measure to `2π` times
real Lebesgue measure. -/
theorem map_log_norm_multiplicativeComplexLebesgue :
    multiplicativeComplexLebesgue.map (fun z : ℂ => Real.log ‖z‖) =
      Real.toNNReal (2 * Real.pi) • (volume : Measure ℝ) := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF measurable_log_norm, multiplicativeComplexLebesgue]
  have hm : Measurable (fun z : ℂ => F (Real.log ‖z‖)) := hF.comp measurable_log_norm
  rw [lintegral_withDensity_eq_lintegral_mul _ measurable_inverseSquareDensity hm]
  change (∫⁻ z : ℂ, inverseSquareDensity z * F (Real.log ‖z‖)) = _
  rw [← Complex.lintegral_comp_polarCoord_symm (fun z => inverseSquareDensity z * F (Real.log ‖z‖))]
  let T := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  let R (r : ℝ) := ENNReal.ofReal r⁻¹ * F (Real.log r)
  have hR : Measurable R := (measurable_id.inv.ennreal_ofReal).mul (hF.comp Real.measurable_log)
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  change (∫⁻ p : ℝ × ℝ in T, ENNReal.ofReal p.1 •
    (inverseSquareDensity (Complex.polarCoord.symm p) * F (Real.log ‖Complex.polarCoord.symm p‖))) = _
  calc
    _ = ∫⁻ p : ℝ × ℝ in T, R p.1 := by
      apply setLIntegral_congr_fun hT
      intro p hp
      have hr : 0 < p.1 := hp.1
      have hn : ‖Complex.polarCoord.symm p‖ = p.1 :=
        (Complex.norm_polarCoord_symm p).trans (abs_of_pos hr)
      simp only [inverseSquareDensity, hn, smul_eq_mul, ← mul_assoc, R]
      rw [← ENNReal.ofReal_mul hr.le]
      congr 2
      field_simp [hr.ne']
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi (0 : ℝ), R r := by
      change (∫⁻ p : ℝ × ℝ, (R ∘ Prod.fst) p ∂((volume : Measure ℝ).prod volume).restrict T) = _
      rw [show T = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl, ← Measure.prod_restrict]
      rw [lintegral_prod _ (hR.comp measurable_fst).aemeasurable]
      simp only [Function.comp_apply, lintegral_const, Measure.restrict_apply_univ,
        Real.volume_Ioo, sub_neg_eq_add, ← two_mul]
      simp_rw [mul_comm (R _)]
      exact lintegral_const_mul _ hR
    _ = _ := by
      rw [lintegral_inverse_mul_log F]
      change _ = ∫⁻ y, F y ∂(ENNReal.ofReal (2 * Real.pi)) • (volume : Measure ℝ)
      rw [lintegral_smul_measure]
      rfl

instance : SigmaFinite multiplicativeComplexLebesgue := by
  unfold multiplicativeComplexLebesgue inverseSquareDensity
  infer_instance

/-- The coordinatewise logarithmic radius of the product multiplicative measure on complex
diagonals is real Lebesgue measure with one factor of `2π` per coordinate. -/
theorem map_log_norm_diagonal (n : ℕ) :
    (Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue)).map
      (fun (z : Fin n → ℂ) j => Real.log ‖z j‖) =
      (Real.toNNReal (2 * Real.pi)) ^ n • (volume : Measure (Fin n → ℝ)) := by
  have hfinite : SigmaFinite (multiplicativeComplexLebesgue.map (fun z : ℂ => Real.log ‖z‖)) := by
    rw [map_log_norm_multiplicativeComplexLebesgue]
    infer_instance
  rw [Measure.pi_map_pi (hμ := fun _ => hfinite) (fun _ => measurable_log_norm.aemeasurable)]
  simp_rw [map_log_norm_multiplicativeComplexLebesgue]
  rw [Langlands.HarmonicAnalysis.pi_nnreal_smul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
