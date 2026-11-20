import Langlands.Global.RankinSelberg.EisensteinMellin
import Langlands.Global.RankinSelberg.EqualAnalyticResidue

/-! # Constant terms on the negative-height scalar fibre -/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands.Global
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Eisenstein

open EqualAnalytic

local instance boundarySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance boundarySchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)

/-- The Mellin weight multiplying the zero-vector term of the theta series. -/
def boundaryWeight (g : Points F (r + 1)) (t : ℂ) (a : Points F 1) : ℂ :=
  ideleChar F χ a * Complex.exp (t * (mellinHeight F r g a : ℂ))

/-- The integral of the Mellin weight over the negative-height part of the fibre. -/
def negativeBoundary (g : Points F (r + 1)) (t : ℂ) : ℂ :=
  ∫ a in (positiveLog F r g)ᶜ, boundaryWeight F r χ g t a ∂ideleQuotientMeasure F

private theorem mem_negativeLog_iff (g : Points F (r + 1)) (a : Points F 1) :
    a ∈ (positiveLog F r g)ᶜ ↔
      logNorm F a < -Real.log (detNorm F (r + 1) g) / (r + 1 : ℝ) := by
  have hn : (0 : ℝ) < r + 1 := by positivity
  change (¬ 0 ≤ mellinHeight F r g a) ↔ _
  rw [not_le, mellinHeight_eq, lt_div_iff₀ hn, Nat.cast_add, Nat.cast_one, mul_comm (logNorm F a)]
  constructor <;> intro h <;> linarith

theorem negativeBoundary_integrable (g : Points F (r + 1)) (t : ℂ) {β C : ℝ}
    (hχ : ∀ a, ‖ideleChar F χ a‖ ≤ C * Real.exp (β * logNorm F a))
    (ht : 0 < β + ((r + 1 : ℕ) : ℝ) * t.re) :
    IntegrableOn (boundaryWeight F r χ g t) (positiveLog F r g)ᶜ (ideleQuotientMeasure F) := by
  let L := Real.log (detNorm F (r + 1) g)
  let c := -L / (r + 1 : ℝ)
  let k := β + ((r + 1 : ℕ) : ℝ) * t.re
  let u : ℝ → ℝ := (Iio c).indicator fun y => Real.exp (k * y)
  have hu : Measurable u :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).indicator measurableSet_Iio
  have huint : Integrable u volume :=
    (integrable_indicator_iff measurableSet_Iio).2 <|
      (integrableOn_Iic_iff_integrableOn_Iio).1 (integrableOn_exp_mul_Iic ht c)
  have hmaj : Integrable (fun a => (C * Real.exp (t.re * L)) * u (logNorm F a))
      (ideleQuotientMeasure F) :=
    ((integrableOn_logNorm_iff F u hu.aestronglyMeasurable).2 huint).const_mul _
  refine (hmaj.integrableOn).mono' ?_ ?_
  · exact ((continuous_ideleChar F χ).measurable.mul (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp
        (measurable_mellinHeight F r g))))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_positiveLog F r g).compl] with a ha
    have hcut : logNorm F a ∈ Iio c := (mem_negativeLog_iff F r g a).1 ha
    rw [boundaryWeight, UnequalAnalytic.norm_mul_cexp, mellinHeight_eq]
    change ‖ideleChar F χ a‖ * Real.exp (t.re * (((r + 1 : ℕ) : ℝ) * logNorm F a + L)) ≤
      (C * Real.exp (t.re * L)) * (Iio c).indicator (fun y => Real.exp (k * y)) (logNorm F a)
    rw [indicator_of_mem hcut]
    calc
      _ ≤ (C * Real.exp (β * logNorm F a)) *
          Real.exp (t.re * (((r + 1 : ℕ) : ℝ) * logNorm F a + L)) :=
        mul_le_mul_of_nonneg_right (hχ a) (Real.exp_pos _).le
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 2
        dsimp only [k]
        ring

private theorem negativeBoundary_eq_integral (g : Points F (r + 1)) (t : ℂ) :
    negativeBoundary F r χ g t =
      Complex.exp (t * (Real.log (detNorm F (r + 1) g) : ℂ)) *
        ∫ a in ideleDomain F, ideleChar F χ a *
          (Iio (-Real.log (detNorm F (r + 1) g) / (r + 1 : ℝ))).indicator
            (fun y : ℝ => Complex.exp (((r + 1 : ℕ) : ℂ) * t * y)) (logNorm F a)
          ∂ideleMeasure F := by
  rw [negativeBoundary, ← integral_indicator (measurableSet_positiveLog F r g).compl,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with a
  by_cases ha : a ∈ (positiveLog F r g)ᶜ
  · have hcut := (mem_negativeLog_iff F r g a).1 ha
    rw [indicator_of_mem ha, indicator_of_mem (show _ ∈ Iio _ from hcut),
      boundaryWeight, mellinHeight_eq, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_natCast, mul_add, Complex.exp_add]
    rw [show t * (((r + 1 : ℕ) : ℂ) * (logNorm F a : ℂ)) =
      ((r + 1 : ℕ) : ℂ) * t * (logNorm F a : ℂ) by ring]
    ring
  · have hcut : logNorm F a ∉ Iio (-Real.log (detNorm F (r + 1) g) / (r + 1 : ℝ)) :=
      fun h => ha ((mem_negativeLog_iff F r g a).2 h)
    rw [indicator_of_notMem ha, indicator_of_notMem hcut, mul_zero, mul_zero]

/-- A character nontrivial on the norm-one ideles kills the constant term. -/
theorem negativeBoundary_eq_zero {z₀ : Points F 1} (hz₀ : detNorm F 1 z₀ = 1)
    (hχ : ideleChar F χ z₀ ≠ 1) (g : Points F (r + 1)) (t : ℂ) :
    negativeBoundary F r χ g t = 0 := by
  rw [negativeBoundary_eq_integral, integral_ideleChar_mul_eq_zero F χ hz₀ hχ, mul_zero]

/-- For a norm power, the constant term has a numerator independent of `t`. -/
theorem negativeBoundary_eq_of_char {w : ℂ}
    (hw : ∀ a, ideleChar F χ a = detPower F 1 a w)
    (g : Points F (r + 1)) (t : ℂ) (ht : 0 < (w + ((r + 1 : ℕ) : ℂ) * t).re) :
    negativeBoundary F r χ g t =
      Complex.exp (-(w / (r + 1 : ℂ)) * (Real.log (detNorm F (r + 1) g) : ℂ)) /
        (w + ((r + 1 : ℕ) : ℂ) * t) := by
  rw [negativeBoundary_eq_integral, inner_char_integral (r := r) hw t _ measurableSet_Iio,
    exp_mul_char_integral_Iio (r + 1) ht, ← mul_div_assoc, exp_combine]

end Langlands.Global.RankinSelbergGlobal.Eisenstein
