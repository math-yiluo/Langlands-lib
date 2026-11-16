import Langlands.Global.RankinSelberg.EqualAnalyticUnfolding

/-! # The residual integrals

Let `P` be invariant under `GL_n(F)` (`n = r + 1`) with `P(a g) = χ(a) P(g)` for scalar ideles,
and `L(g) = log |det g|`. For the integrals over `GL_n(F) \ GL_n(𝔸)`

`c(t) = ∫_(L < 0) P e^(t L)` and `d(t) = ∫_(L ≥ 0) P e^(t L)`

(assumed absolutely convergent), with `C_w = ∫_(D ∩ S) P(g) |det g|^(-w/n) dg`:

* if `χ(a) = |a|^w` for all `a`, then `c(t) = C_w / (n t + w)` when `Re(w + n t) > 0`
  (`residueLt_eq_of_char`) and `d(t) = -C_w / (n t + w)` when `Re(w + n t) < 0`
  (`residueGe_eq_of_char`);
* if `χ(z₀) ≠ 1` for some `z₀` of norm one, then `c(t) = d(t) = 0`
  (`residueLt_eq_zero`, `residueGe_eq_zero`).

The proof fibres over the centre and evaluates `∫_(F^× \ 𝔸^×)` through `log |a|`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance residueSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance residueSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

/-- The integrand `P e^(t L)` on `L < 0`. -/
def resLt (P : Points F (r + 1) → ℂ) (t : ℂ) (g : Points F (r + 1)) : ℂ :=
  if Real.log (detNorm F (r + 1) g) < 0 then
    P g * Complex.exp (t * (Real.log (detNorm F (r + 1) g) : ℂ)) else 0

/-- The integrand `P e^(t L)` on `L ≥ 0`. -/
def resGe (P : Points F (r + 1) → ℂ) (t : ℂ) (g : Points F (r + 1)) : ℂ :=
  if 0 ≤ Real.log (detNorm F (r + 1) g) then
    P g * Complex.exp (t * (Real.log (detNorm F (r + 1) g) : ℂ)) else 0

/-- The constant `C_w = ∫_(D ∩ S) P(g) |det g|^(-w/n) dg`. -/
def residueConstant (P : Points F (r + 1) → ℂ) (w : ℂ) : ℂ :=
  ∫ g in glDomain F (r + 1) ∩ glSlab F (r + 1),
    P g * Complex.exp (-(w / (r + 1 : ℂ)) * (Real.log (detNorm F (r + 1) g) : ℂ)) ∂Measure.haar

variable {F r}

theorem resLt_rational_mul {P : Points F (r + 1) → ℂ}
    (hP : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g) (t : ℂ)
    (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    resLt F r P t (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = resLt F r P t g := by
  simp only [resLt, UnequalAnalytic.detNorm_rational_mul, hP]

theorem resGe_rational_mul {P : Points F (r + 1) → ℂ}
    (hP : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g) (t : ℂ)
    (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    resGe F r P t (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = resGe F r P t g := by
  simp only [resGe, UnequalAnalytic.detNorm_rational_mul, hP]

theorem measurable_resLt {P : Points F (r + 1) → ℂ} (hP : Continuous P) (t : ℂ) :
    Measurable (resLt F r P t) := by
  have hL := Real.measurable_log.comp (UnequalAnalytic.continuous_detNorm F (r + 1)).measurable
  refine Measurable.ite (measurableSet_lt hL measurable_const) ?_ measurable_const
  exact hP.measurable.mul (Complex.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp hL)))

theorem measurable_resGe {P : Points F (r + 1) → ℂ} (hP : Continuous P) (t : ℂ) :
    Measurable (resGe F r P t) := by
  have hL := Real.measurable_log.comp (UnequalAnalytic.continuous_detNorm F (r + 1)).measurable
  refine Measurable.ite (measurableSet_le measurable_const hL) ?_ measurable_const
  exact hP.measurable.mul (Complex.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp hL)))

/-- The fibred value of `resLt`. -/
theorem resLt_zeta_mul {P : Points F (r + 1) → ℂ} {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g) (t : ℂ) (a : Points F 1)
    (g : Points F (r + 1)) :
    resLt F r P t (zeta F (r + 1) a * g) =
      P g * Complex.exp (t * (Real.log (detNorm F (r + 1) g) : ℂ)) *
        (ideleChar F χ a * (Iio (-(Real.log (detNorm F (r + 1) g)) / (r + 1 : ℝ))).indicator
          (fun y : ℝ => Complex.exp (((r + 1 : ℕ) : ℂ) * t * y)) (logNorm F a)) := by
  have hn : (0 : ℝ) < r + 1 := by positivity
  rw [resLt, log_detNorm_zeta_mul, hcent]
  by_cases h : ((r + 1 : ℕ) : ℝ) * logNorm F a + Real.log (detNorm F (r + 1) g) < 0
  · have h' : logNorm F a ∈ Iio (-(Real.log (detNorm F (r + 1) g)) / (r + 1 : ℝ)) := by
      rw [mem_Iio, lt_div_iff₀ hn]
      push_cast at h
      linarith
    rw [Set.indicator_of_mem h']
    simp only [h, ↓reduceIte]
    push_cast
    rw [show t * ((r + 1 : ℂ) * (logNorm F a : ℂ) + (Real.log (detNorm F (r + 1) g) : ℂ)) =
      (r + 1 : ℂ) * t * (logNorm F a : ℂ) + t * (Real.log (detNorm F (r + 1) g) : ℂ) by ring,
      Complex.exp_add]
    ring
  · have h' : logNorm F a ∉ Iio (-(Real.log (detNorm F (r + 1) g)) / (r + 1 : ℝ)) := by
      rw [mem_Iio, lt_div_iff₀ hn]
      push_cast at h
      linarith
    rw [Set.indicator_of_notMem h']
    simp only [h, ↓reduceIte]
    ring

/-- The fibred value of `resGe`. -/
theorem resGe_zeta_mul {P : Points F (r + 1) → ℂ} {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g) (t : ℂ) (a : Points F 1)
    (g : Points F (r + 1)) :
    resGe F r P t (zeta F (r + 1) a * g) =
      P g * Complex.exp (t * (Real.log (detNorm F (r + 1) g) : ℂ)) *
        (ideleChar F χ a * (Ici (-(Real.log (detNorm F (r + 1) g)) / (r + 1 : ℝ))).indicator
          (fun y : ℝ => Complex.exp (((r + 1 : ℕ) : ℂ) * t * y)) (logNorm F a)) := by
  have hn : (0 : ℝ) < r + 1 := by positivity
  rw [resGe, log_detNorm_zeta_mul, hcent]
  by_cases h : 0 ≤ ((r + 1 : ℕ) : ℝ) * logNorm F a + Real.log (detNorm F (r + 1) g)
  · have h' : logNorm F a ∈ Ici (-(Real.log (detNorm F (r + 1) g)) / (r + 1 : ℝ)) := by
      rw [mem_Ici, div_le_iff₀ hn]
      push_cast at h
      linarith
    rw [Set.indicator_of_mem h']
    simp only [h, ↓reduceIte]
    push_cast
    rw [show t * ((r + 1 : ℂ) * (logNorm F a : ℂ) + (Real.log (detNorm F (r + 1) g) : ℂ)) =
      (r + 1 : ℂ) * t * (logNorm F a : ℂ) + t * (Real.log (detNorm F (r + 1) g) : ℂ) by ring,
      Complex.exp_add]
    ring
  · have h' : logNorm F a ∉ Ici (-(Real.log (detNorm F (r + 1) g)) / (r + 1 : ℝ)) := by
      rw [mem_Ici, div_le_iff₀ hn]
      push_cast at h
      linarith
    rw [Set.indicator_of_notMem h']
    simp only [h, ↓reduceIte]
    ring

/-- Fibring a residual integral over the centre. -/
theorem integral_res_fibre (n : ℕ) (hn : 0 < n) {f : Points F n → ℂ} (hfm : Measurable f)
    (hf : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      f (AdelicGroupPoints.rational F (Scheme F n) c * g) = f g)
    (hint : Integrable (fun x => f (Quotient.out x))
      (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n))) :
    ∫ x, f (Quotient.out x) ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) =
      ∫ g in glDomain F n ∩ glSlab F n, ∫ a in ideleDomain F, f (zeta F n a * g)
        ∂ideleMeasure F ∂Measure.haar := by
  have hf' : ∀ (c : glRational F n) (g : Points F n), f ((c : Points F n) * g) = f g := by
    rintro ⟨_, c, rfl⟩ g
    exact hf c g
  have hfun : (fun x : AdelicGroupPoints.RationalQuotient F (Scheme F n) => f (Quotient.out x)) =
      LeftCosetSpace.lift (glRational F n) f hf' :=
    funext fun x => (UnequalAnalytic.lift_eq_out _ f hf' x).symm
  have hm : Measurable (LeftCosetSpace.lift (glRational F n) f hf') :=
    measurable_from_quotient.2 hfm
  rw [hfun] at hint ⊢
  rw [integral_rationalQuotient_eq F n hn hm.aestronglyMeasurable hint]
  rfl

theorem exp_mul_char_integral_Iio {w t : ℂ} (n : ℕ) (ht : 0 < (w + n * t).re)
    (c : ℝ) : ∫ y : ℝ, (Iio c).indicator (fun y : ℝ => Complex.exp (w * y) *
      Complex.exp (n * t * y)) y = Complex.exp ((w + n * t) * c) / (w + n * t) := by
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    ← integral_exp_mul_complex_Iic ht c]
  refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
  rw [← Complex.exp_add]
  ring_nf

theorem exp_mul_char_integral_Ici {w t : ℂ} (n : ℕ) (ht : (w + n * t).re < 0)
    (c : ℝ) : ∫ y : ℝ, (Ici c).indicator (fun y : ℝ => Complex.exp (w * y) *
      Complex.exp (n * t * y)) y = -Complex.exp ((w + n * t) * c) / (w + n * t) := by
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    ← integral_exp_mul_complex_Ioi ht c]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [← Complex.exp_add]
  ring_nf

theorem exp_combine (L : ℝ) (t w : ℂ) (r : ℕ) :
    Complex.exp (t * (L : ℂ)) * Complex.exp ((w + ((r + 1 : ℕ) : ℂ) * t) *
      ((-L / (r + 1 : ℝ) : ℝ) : ℂ)) = Complex.exp (-(w / (r + 1 : ℂ)) * (L : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  have hn : (r + 1 : ℂ) ≠ 0 := by
    have : ((r + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
    exact_mod_cast this
  push_cast
  field_simp
  ring

/-- The inner integral over `F^× \ 𝔸^×` when `χ = |·|^w`. -/
theorem inner_char_integral {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} {w : ℂ}
    (hw : ∀ z, ideleChar F χ z = detPower F 1 z w) (t : ℂ) (S : Set ℝ) (hS : MeasurableSet S) :
    ∫ a in ideleDomain F, ideleChar F χ a *
        S.indicator (fun y : ℝ => Complex.exp (((r + 1 : ℕ) : ℂ) * t * y)) (logNorm F a)
          ∂ideleMeasure F =
      ∫ y : ℝ, S.indicator (fun y : ℝ => Complex.exp (w * y) *
        Complex.exp (((r + 1 : ℕ) : ℂ) * t * y)) y := by
  have h : ∀ a, ideleChar F χ a *
      S.indicator (fun y : ℝ => Complex.exp (((r + 1 : ℕ) : ℂ) * t * y)) (logNorm F a) =
      S.indicator (fun y : ℝ => Complex.exp (w * y) *
        Complex.exp (((r + 1 : ℕ) : ℂ) * t * y)) (logNorm F a) := by
    intro a
    rw [hw, detPower_one_eq]
    by_cases ha : logNorm F a ∈ S
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero]
  simp only [h]
  refine integral_logNorm F _ ?_
  exact ((Measurable.indicator ((Complex.measurable_exp.comp (measurable_const.mul
    Complex.measurable_ofReal)).mul (Complex.measurable_exp.comp (measurable_const.mul
      Complex.measurable_ofReal))) hS)).aestronglyMeasurable

/-- **The residual integral on `|det| < 1` when `χ = |·|^w`.** -/
theorem residueLt_eq_of_char {P : Points F (r + 1) → ℂ} (hPc : Continuous P)
    (hPr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g)
    {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g)
    {w : ℂ} (hw : ∀ z, ideleChar F χ z = detPower F 1 z w) {t : ℂ}
    (ht : 0 < (w + ((r + 1 : ℕ) : ℂ) * t).re)
    (hint : Integrable (fun x => resLt F r P t (Quotient.out x))
      (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)))) :
    ∫ x, resLt F r P t (Quotient.out x)
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)) =
      residueConstant F r P w / (((r + 1 : ℕ) : ℂ) * t + w) := by
  rw [integral_res_fibre (r + 1) (Nat.succ_pos r) (measurable_resLt hPc t)
    (resLt_rational_mul hPr t) hint, residueConstant, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [resLt_zeta_mul hcent]
  rw [integral_const_mul]
  rw [inner_char_integral (r := r) hw t _ measurableSet_Iio,
    exp_mul_char_integral_Iio (r + 1) ht, ← exp_combine, add_comm w]
  ring

/-- **The residual integral on `|det| ≥ 1` when `χ = |·|^w`.** -/
theorem residueGe_eq_of_char {P : Points F (r + 1) → ℂ} (hPc : Continuous P)
    (hPr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g)
    {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g)
    {w : ℂ} (hw : ∀ z, ideleChar F χ z = detPower F 1 z w) {t : ℂ}
    (ht : (w + ((r + 1 : ℕ) : ℂ) * t).re < 0)
    (hint : Integrable (fun x => resGe F r P t (Quotient.out x))
      (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)))) :
    ∫ x, resGe F r P t (Quotient.out x)
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)) =
      -residueConstant F r P w / (((r + 1 : ℕ) : ℂ) * t + w) := by
  rw [integral_res_fibre (r + 1) (Nat.succ_pos r) (measurable_resGe hPc t)
    (resGe_rational_mul hPr t) hint, residueConstant, ← integral_neg, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [resGe_zeta_mul hcent]
  rw [integral_const_mul]
  rw [inner_char_integral (r := r) hw t _ measurableSet_Ici,
    exp_mul_char_integral_Ici (r + 1) ht, ← exp_combine, add_comm w]
  ring

/-- **The residual integral on `|det| < 1` vanishes for `χ` nontrivial on norm one.** -/
theorem residueLt_eq_zero {P : Points F (r + 1) → ℂ} (hPc : Continuous P)
    (hPr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g)
    {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g)
    {z₀ : Points F 1} (hz₀ : detNorm F 1 z₀ = 1) (hχ : ideleChar F χ z₀ ≠ 1) (t : ℂ)
    (hint : Integrable (fun x => resLt F r P t (Quotient.out x))
      (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)))) :
    ∫ x, resLt F r P t (Quotient.out x)
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)) = 0 := by
  rw [integral_res_fibre (r + 1) (Nat.succ_pos r) (measurable_resLt hPc t)
    (resLt_rational_mul hPr t) hint]
  have h0 : ∀ g : Points F (r + 1),
      ∫ a in ideleDomain F, resLt F r P t (zeta F (r + 1) a * g) ∂ideleMeasure F = 0 := by
    intro g
    simp only [resLt_zeta_mul hcent]
    rw [integral_const_mul, integral_ideleChar_mul_eq_zero F χ hz₀ hχ, mul_zero]
  simp only [h0, integral_zero]

/-- **The residual integral on `|det| ≥ 1` vanishes for `χ` nontrivial on norm one.** -/
theorem residueGe_eq_zero {P : Points F (r + 1) → ℂ} (hPc : Continuous P)
    (hPr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g)
    {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g)
    {z₀ : Points F 1} (hz₀ : detNorm F 1 z₀ = 1) (hχ : ideleChar F χ z₀ ≠ 1) (t : ℂ)
    (hint : Integrable (fun x => resGe F r P t (Quotient.out x))
      (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)))) :
    ∫ x, resGe F r P t (Quotient.out x)
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)) = 0 := by
  rw [integral_res_fibre (r + 1) (Nat.succ_pos r) (measurable_resGe hPc t)
    (resGe_rational_mul hPr t) hint]
  have h0 : ∀ g : Points F (r + 1),
      ∫ a in ideleDomain F, resGe F r P t (zeta F (r + 1) a * g) ∂ideleMeasure F = 0 := by
    intro g
    simp only [resGe_zeta_mul hcent]
    rw [integral_const_mul, integral_ideleChar_mul_eq_zero F χ hz₀ hχ, mul_zero]
  simp only [h0, integral_zero]

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
