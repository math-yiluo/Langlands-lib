import Langlands.Global.RankinSelberg.ArchimedeanMellinPair
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Inverse Mellin transforms of functions decaying in vertical strips

See the paired Markdown file.
-/

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology FourierTransform Real

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin

open ArchimedeanMellinPair

/-- Decay like `(1 + y²)⁻¹` on every vertical strip `a ≤ Re s ≤ b`. -/
def StripDecay (m : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C : ℝ, ∀ x : ℝ, a ≤ x → x ≤ b → ∀ y : ℝ,
    ‖m (x + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹

theorem integrable_vertical {f : ℂ → ℂ} (hf : Continuous f) {x C : ℝ}
    (hC : ∀ y : ℝ, ‖f (x + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹) :
    Integrable (fun y : ℝ => f (x + y * I)) := by
  refine (integrable_inv_one_add_sq.const_mul C).mono' ?_ (Eventually.of_forall hC)
  exact (hf.comp (by fun_prop)).aestronglyMeasurable

theorem tendsto_inv_one_add_sq : Tendsto (fun T : ℝ => (1 + T ^ 2)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero))

/-- Contour shift between two vertical lines for an entire function decaying like
`(1 + y²)⁻¹` uniformly on the strip between them. -/
theorem integral_vertical_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b C : ℝ} (hab : a ≤ b)
    (hC : ∀ x : ℝ, a ≤ x → x ≤ b → ∀ y : ℝ, ‖f (x + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹) :
    ∫ y : ℝ, f (a + y * I) = ∫ y : ℝ, f (b + y * I) := by
  have hia := integrable_vertical hf.continuous (hC a le_rfl hab)
  have hib := integrable_vertical hf.continuous (hC b hab le_rfl)
  have hrect : ∀ T : ℝ, I • ((∫ y in (-T)..T, f (b + y * I)) - ∫ y in (-T)..T, f (a + y * I)) =
      (∫ x in a..b, f (x + T * I)) - ∫ x in a..b, f (x + (-T) * I) := by
    intro T
    have := integral_boundary_rect_eq_zero_of_differentiableOn f (Complex.mk a (-T))
      (Complex.mk b T) hf.differentiableOn
    simp only [smul_eq_mul] at this ⊢
    push_cast at this
    linear_combination this
  have hhor : ∀ T : ℝ, ‖∫ x in a..b, f (x + T * I)‖ ≤ C * (1 + T ^ 2)⁻¹ * |b - a| := by
    intro T
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hab] at hx
    exact hC x hx.1.le hx.2 T
  have hlim1 : Tendsto (fun T : ℝ =>
      I • ((∫ y in (-T)..T, f (b + y * I)) - ∫ y in (-T)..T, f (a + y * I))) atTop
      (𝓝 (I • ((∫ y : ℝ, f (b + y * I)) - ∫ y : ℝ, f (a + y * I)))) :=
    ((intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id)).const_smul I
  have hlim2 : Tendsto (fun T : ℝ =>
      I • ((∫ y in (-T)..T, f (b + y * I)) - ∫ y in (-T)..T, f (a + y * I))) atTop (𝓝 0) := by
    simp_rw [hrect]
    refine squeeze_zero_norm (a := fun T : ℝ => 2 * (C * (1 + T ^ 2)⁻¹ * |b - a|))
      (fun T => ?_) ?_
    · refine (norm_sub_le _ _).trans ?_
      have h1 := hhor T
      have h2 := hhor (-T)
      rw [neg_sq] at h2
      push_cast at h2
      linarith
    · have := ((tendsto_inv_one_add_sq.const_mul C).mul_const |b - a|).const_mul 2
      simpa using this
  have h0 := tendsto_nhds_unique hlim1 hlim2
  rw [smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 I_ne_zero
  · exact (sub_eq_zero.1 h0).symm

theorem norm_ofReal_cpow_neg {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    ‖(t : ℂ) ^ (-((x : ℂ) + y * I))‖ = t ^ (-x) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  congr 1
  simp

theorem rpow_neg_le_add {t : ℝ} (ht : 0 < t) {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    t ^ (-x) ≤ t ^ (-a) + t ^ (-b) := by
  have ha := (Real.rpow_pos_of_pos ht (-a)).le
  have hb := (Real.rpow_pos_of_pos ht (-b)).le
  rcases le_total t 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ht h (neg_le_neg hxb)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (neg_le_neg hax)
    linarith

/-- The inverse Mellin transform of an entire function with strip decay does not depend on
the vertical line. -/
theorem mellinInv_eq_of_stripDecay {m : ℂ → ℂ} (hm : Differentiable ℂ m)
    (hdec : StripDecay m) {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    mellinInv a m t = mellinInv b m t := by
  wlog hab : a ≤ b generalizing a b
  · exact (this b a (le_of_not_ge hab)).symm
  obtain ⟨C, hC⟩ := hdec a b
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  have hf : Differentiable ℂ (fun s : ℂ => (t : ℂ) ^ (-s) * m s) := fun s =>
    ((differentiableAt_id.neg).const_cpow (Or.inl ht0)).mul (hm s)
  have hbound : ∀ x : ℝ, a ≤ x → x ≤ b → ∀ y : ℝ,
      ‖(fun s : ℂ => (t : ℂ) ^ (-s) * m s) (x + y * I)‖ ≤
        (C * (t ^ (-a) + t ^ (-b))) * (1 + y ^ 2)⁻¹ := by
    intro x hax hxb y
    simp only
    rw [norm_mul, norm_ofReal_cpow_neg ht]
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC x hax hxb 0)
      have hp : 0 < (1 + (0 : ℝ) ^ 2)⁻¹ := by norm_num
      exact nonneg_of_mul_nonneg_left this hp
    have h1 := rpow_neg_le_add ht hax hxb
    have h2 := hC x hax hxb y
    have hp : 0 ≤ t ^ (-x) := (Real.rpow_pos_of_pos ht _).le
    calc t ^ (-x) * ‖m (x + y * I)‖ ≤ (t ^ (-a) + t ^ (-b)) * (C * (1 + y ^ 2)⁻¹) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have := integral_vertical_eq hf hab hbound
  simp only [mellinInv, smul_eq_mul]
  rw [this]

theorem norm_mellinInv_le (m : ℂ → ℂ) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖mellinInv c m t‖ ≤ (1 / (2 * π)) * (∫ y : ℝ, ‖m (c + y * I)‖) * t ^ (-c) := by
  rw [mellinInv, norm_smul]
  have hcongr : ∀ y : ℝ, ‖(t : ℂ) ^ (-((c : ℂ) + y * I)) • m (c + y * I)‖ =
      t ^ (-c) * ‖m (c + y * I)‖ := by
    intro y
    rw [norm_smul, norm_ofReal_cpow_neg ht]
  have hpi : ‖(1 / (2 * π) : ℝ)‖ = 1 / (2 * π) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖(1 / (2 * π) : ℝ)‖ * ‖∫ y : ℝ, (t : ℂ) ^ (-((c : ℂ) + y * I)) • m (c + y * I)‖
      ≤ (1 / (2 * π)) * ∫ y : ℝ, ‖(t : ℂ) ^ (-((c : ℂ) + y * I)) • m (c + y * I)‖ := by
        rw [hpi]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = _ := by
        simp_rw [hcongr]
        rw [integral_const_mul]
        ring

theorem measurable_mellinInv {m : ℂ → ℂ} (hm : Continuous m) (c : ℝ) :
    Measurable (mellinInv c m) := by
  have hv : Measurable (fun p : ℝ × ℝ => (c : ℂ) + (p.2 : ℂ) * I) :=
    measurable_const.add ((Complex.measurable_ofReal.comp measurable_snd).mul_const I)
  have hmeas : StronglyMeasurable (Function.uncurry fun (t y : ℝ) =>
      (t : ℂ) ^ (-((c : ℂ) + y * I)) • m (c + y * I)) := by
    apply Measurable.stronglyMeasurable
    have h1 : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (-((c : ℂ) + (p.2 : ℂ) * I))) :=
      (Complex.measurable_ofReal.comp measurable_fst).pow hv.neg
    have h2 : Measurable (fun p : ℝ × ℝ => m ((c : ℂ) + (p.2 : ℂ) * I)) :=
      hm.measurable.comp hv
    exact h1.smul h2
  have := hmeas.integral_prod_right (ν := (volume : Measure ℝ))
  exact this.measurable.const_smul _

/-- The inverse Mellin transform on `Re s = 0` of an entire function with strip decay is
rapidly decreasing. -/
theorem rapidDecay_mellinInv {m : ℂ → ℂ} (hm : Differentiable ℂ m) (hdec : StripDecay m) :
    RapidDecay (mellinInv 0 m) := by
  intro M
  refine ⟨(1 / (2 * π)) * ∫ y : ℝ, ‖m ((-M : ℝ) + y * I)‖, fun t ht => ?_⟩
  rw [mellinInv_eq_of_stripDecay hm hdec ht 0 (-M)]
  have := norm_mellinInv_le m (-M) ht
  rwa [neg_neg] at this

theorem exp_neg_abs_le (u : ℝ) : Real.exp (-|u|) ≤ 2 * (1 + u ^ 2)⁻¹ := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg u)
  rw [sq_abs] at h
  have hpos : 0 < 1 + u ^ 2 := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, inv_le_comm₀ (Real.exp_pos _) (by positivity),
    inv_div]
  have := abs_nonneg u
  nlinarith

/-- The Mellin transform of the inverse Mellin transform of an entire function with strip
decay is the function itself. -/
theorem mellin_mellinInv {m : ℂ → ℂ} (hm : Differentiable ℂ m) (hdec : StripDecay m)
    (s : ℂ) : mellin (mellinInv 0 m) s = m s := by
  set c := s.re with hc
  set h := mellinInv 0 m with hh
  set g : ℝ → ℂ := fun y => m ((c : ℂ) + 2 * π * y * I) with hg
  set G : ℝ → ℂ := fun u => Real.exp (-c * u) • h (Real.exp (-u)) with hG
  have hGg : G = 𝓕⁻ g := by
    funext u
    have hx : 0 < Real.exp (-u) := Real.exp_pos _
    simp only [hG, hh]
    rw [mellinInv_eq_of_stripDecay hm hdec hx 0 c, mellinInv_eq_fourierInv c m hx,
      Real.log_exp, neg_neg, ← smul_assoc]
    have : (Real.exp (-c * u) : ℝ) • ((Real.exp (-u) : ℝ) : ℂ) ^ (-(c : ℂ)) = 1 := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hx.le, ← Real.exp_mul,
        Complex.real_smul, ← Complex.ofReal_mul, ← Real.exp_add,
        show -c * u + -u * -c = 0 by ring, Real.exp_zero, Complex.ofReal_one]
    rw [this, one_smul]
  -- integrability of `g`
  obtain ⟨C, hC⟩ := hdec c c
  have hgi : Integrable g := by
    have h1 := integrable_vertical hm.continuous (hC c le_rfl le_rfl)
    have h2 := h1.comp_mul_left' (show (2 * π : ℝ) ≠ 0 by positivity)
    refine h2.congr (Eventually.of_forall fun y => ?_)
    simp only [hg]
    push_cast
    ring_nf
  -- integrability of `G`
  have hmeas : Measurable h := measurable_mellinInv hm.continuous 0
  have hdecay := rapidDecay_mellinInv hm hdec
  obtain ⟨C₁, hC₁⟩ := hdecay (1 - c)
  obtain ⟨C₂, hC₂⟩ := hdecay (-1 - c)
  have hGb : ∀ u : ℝ, ‖G u‖ ≤ 2 * (|C₁| + |C₂|) * (1 + u ^ 2)⁻¹ := by
    intro u
    have hx : 0 < Real.exp (-u) := Real.exp_pos _
    simp only [hG, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hE := exp_neg_abs_le u
    have hEpos : 0 < Real.exp (-|u|) := Real.exp_pos _
    rcases le_total 0 u with hu | hu
    · have := hC₁ _ hx
      rw [← Real.exp_mul] at this
      have hkey : Real.exp (-c * u) * ‖h (Real.exp (-u))‖ ≤ |C₁| * Real.exp (-|u|) := by
        calc Real.exp (-c * u) * ‖h (Real.exp (-u))‖
            ≤ Real.exp (-c * u) * (C₁ * Real.exp (-u * (1 - c))) :=
              mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
          _ = C₁ * Real.exp (-|u|) := by
              rw [abs_of_nonneg hu, mul_left_comm, ← Real.exp_add]
              ring_nf
          _ ≤ |C₁| * Real.exp (-|u|) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hEpos.le
      calc _ ≤ |C₁| * Real.exp (-|u|) := hkey
        _ ≤ |C₁| * (2 * (1 + u ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hE (abs_nonneg _)
        _ ≤ 2 * (|C₁| + |C₂|) * (1 + u ^ 2)⁻¹ := by
            have : 0 ≤ (1 + u ^ 2)⁻¹ := by positivity
            nlinarith [abs_nonneg C₂]
    · have := hC₂ _ hx
      rw [← Real.exp_mul] at this
      have hkey : Real.exp (-c * u) * ‖h (Real.exp (-u))‖ ≤ |C₂| * Real.exp (-|u|) := by
        calc Real.exp (-c * u) * ‖h (Real.exp (-u))‖
            ≤ Real.exp (-c * u) * (C₂ * Real.exp (-u * (-1 - c))) :=
              mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
          _ = C₂ * Real.exp (-|u|) := by
              rw [abs_of_nonpos hu, mul_left_comm, ← Real.exp_add]
              ring_nf
          _ ≤ |C₂| * Real.exp (-|u|) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hEpos.le
      calc _ ≤ |C₂| * Real.exp (-|u|) := hkey
        _ ≤ |C₂| * (2 * (1 + u ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hE (abs_nonneg _)
        _ ≤ 2 * (|C₁| + |C₂|) * (1 + u ^ 2)⁻¹ := by
            have : 0 ≤ (1 + u ^ 2)⁻¹ := by positivity
            nlinarith [abs_nonneg C₁]
  have hGi : Integrable G := by
    refine (integrable_inv_one_add_sq.const_mul _).mono' ?_ (Eventually.of_forall hGb)
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).smul
      (hmeas.comp (Real.measurable_exp.comp measurable_neg))).aestronglyMeasurable
  have hFgi : Integrable (𝓕 g) := by
    have : 𝓕 g = fun v => G (-v) := by
      funext v
      rw [hGg, Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [this]
    exact hGi.comp_neg
  have hcont : ContinuousAt g (s.im / (2 * π)) :=
    (hm.continuous.comp (by fun_prop)).continuousAt
  rw [mellin_eq_fourier, ← hc]
  change 𝓕 G (s.im / (2 * π)) = m s
  rw [hGg, hgi.fourier_fourierInv_eq hFgi hcont]
  simp only [hg]
  have hpi : (2 * π : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
  congr 1
  rw [hc]
  push_cast
  field_simp
  exact re_add_im s

/-- An entire function with strip decay is the Mellin transform of a measurable rapidly
decreasing function. -/
theorem exists_mellin_eq {m : ℂ → ℂ} (hm : Differentiable ℂ m) (hdec : StripDecay m) :
    ∃ h : ℝ → ℂ, Measurable h ∧ RapidDecay h ∧ ∀ s : ℂ, mellin h s = m s :=
  ⟨mellinInv 0 m, measurable_mellinInv hm.continuous 0, rapidDecay_mellinInv hm hdec,
    mellin_mellinInv hm hdec⟩

end Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin
