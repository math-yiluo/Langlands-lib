import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-! # A square bound for integrable kernels -/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace Langlands.Global

/-- Integrating a complex kernel of finite absolute mass against a jointly measurable family
with a uniform squared-norm integral gives a function with integrable squared norm. -/
theorem integrable_sq_norm_kernelIntegral {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {κ : X → ℂ} (hκ : Measurable κ) (hκint : Integrable κ μ)
    {f : X → Y → ℂ} (hf : Measurable (fun xy : X × Y => f xy.1 xy.2))
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hsection : ∀ x, ∫⁻ y, ‖f x y‖ₑ ^ 2 ∂ν ≤ B) :
    Integrable (fun y => ‖∫ x, κ x * f x y ∂μ‖ ^ 2) ν := by
  let μκ := μ.withDensity (fun x => ‖κ x‖ₑ)
  have : IsFiniteMeasure μκ := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (hasFiniteIntegral_iff_enorm.mp hκint.hasFiniteIntegral)
  let mass := μκ Set.univ
  let s (x : X) (y : Y) := ‖f x y‖ₑ ^ 2
  have hs : Measurable (fun xy : X × Y => s xy.1 xy.2) := hf.enorm.pow_const 2
  have hpoint (y : Y) : ‖∫ x, κ x * f x y ∂μ‖ₑ ^ 2 ≤ mass * ∫⁻ x, s x y ∂μκ := by
    have hfy : Measurable (fun x => ‖f x y‖ₑ) := hf.enorm.comp (measurable_id.prodMk measurable_const)
    have hnorm : ‖∫ x, κ x * f x y ∂μ‖ₑ ≤ ∫⁻ x, ‖f x y‖ₑ ∂μκ := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hκ.enorm hfy]
      simpa only [enorm_mul, Pi.mul_apply] using
        (enorm_integral_le_lintegral_enorm (μ := μ) (fun x => κ x * f x y))
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μκ Real.HolderConjugate.two_two
      (f := fun _ => (1 : ℝ≥0∞)) (g := fun x => ‖f x y‖ₑ)
      measurable_const.aemeasurable hfy.aemeasurable
    have hhalf : (∫⁻ x, ‖f x y‖ₑ ∂μκ) ≤ mass ^ (1 / 2 : ℝ) * (∫⁻ x, s x y ∂μκ) ^ (1 / 2 : ℝ) := by
      simpa [mass, s, Pi.mul_apply, ENNReal.rpow_natCast] using hholder
    refine (pow_le_pow_left' (hnorm.trans hhalf) 2).trans_eq ?_
    rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
  have hmeas : StronglyMeasurable (fun y => ∫ x, κ x * f x y ∂μ) :=
    ((hκ.comp measurable_fst).mul hf).stronglyMeasurable.integral_prod_left
  refine ⟨(hmeas.norm.pow 2).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  have hbound : (∫⁻ y, ‖∫ x, κ x * f x y ∂μ‖ₑ ^ 2 ∂ν) ≤ mass * (mass * B) := by
    calc
      _ ≤ ∫⁻ y, mass * ∫⁻ x, s x y ∂μκ ∂ν := lintegral_mono hpoint
      _ = mass * ∫⁻ x, ∫⁻ y, s x y ∂ν ∂μκ := by
        rw [lintegral_const_mul _ hs.lintegral_prod_left',
          lintegral_lintegral_swap (f := fun y x => s x y)
            (show Measurable (fun yx : Y × X => s yx.2 yx.1) from
              hs.comp measurable_swap).aemeasurable]
      _ ≤ mass * (mass * B) := by
        gcongr
        exact (lintegral_mono hsection).trans_eq (by rw [lintegral_const, mul_comm])
  have hfinite : mass * (mass * B) < ∞ :=
    ENNReal.mul_lt_top (measure_lt_top _ _) (ENNReal.mul_lt_top (measure_lt_top _ _) hB.lt_top)
  have hsq (z : ℂ) : ‖(‖z‖ ^ 2 : ℝ)‖ₑ = ‖z‖ₑ ^ 2 := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg ‖z‖),
      ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm]
  simpa only [hsq] using hbound.trans_lt hfinite

end Langlands.Global
