import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Determination by Gaussian-weighted directional moments -/

noncomputable section

open MeasureTheory Complex

set_option autoImplicit false

namespace Langlands.Analysis.GaussianWeightedMoment

variable {H E : Type*} [MeasurableSpace H] {ν : Measure H}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {p : H → E} {F : H → ℂ}

omit [MeasurableSpace E] [BorelSpace E] in
private theorem exp_linear_sub_sq_le (L : E →L[ℝ] ℝ) (x : E) :
    Real.exp (‖L x‖ - ‖x‖ ^ 2) ≤ Real.exp (‖L‖ ^ 2 / 2) * Real.exp (-‖x‖ ^ 2 / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [L.le_opNorm x, sq_nonneg (‖L‖ - ‖x‖)]

private theorem integrable_exp_times_gaussian (hp : Measurable p) (hF : Measurable F)
    (hthin : Integrable (fun h => (Real.exp (-‖p h‖ ^ 2 / 2) : ℂ) * F h) ν)
    (L : E →L[ℝ] ℝ) :
    Integrable (fun h => Real.exp ‖L (p h)‖ * ‖(Real.exp (-‖p h‖ ^ 2) : ℂ) * F h‖) ν := by
  have hLp : Measurable (fun h => L (p h)) := L.continuous.measurable.comp hp
  refine (hthin.norm.const_mul (Real.exp (‖L‖ ^ 2 / 2))).mono' (by fun_prop) <|
    Filter.Eventually.of_forall fun h => ?_
  simp only [Real.norm_eq_abs, abs_norm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← sub_eq_add_neg]
  exact mul_le_mul_of_nonneg_right (exp_linear_sub_sq_le L (p h)) (norm_nonneg _)

private theorem integrable_moment {r : H → ℝ} {w : H → ℂ}
    (hr : Measurable r) (hw : Measurable w)
    (hbound : Integrable (fun h => Real.exp ‖r h‖ * ‖w h‖) ν) (n : ℕ) :
    Integrable (fun h => (r h : ℂ) ^ n * w h) ν := by
  refine (hbound.const_mul (n.factorial : ℝ)).mono' (by fun_prop) <|
    Filter.Eventually.of_forall fun h => ?_
  simp only [norm_mul, norm_pow, Complex.norm_real]
  rw [← mul_assoc, mul_comm (n.factorial : ℝ)]
  exact mul_le_mul_of_nonneg_right
    ((div_le_iff₀ (Nat.cast_pos.mpr n.factorial_pos)).mp
      (Real.pow_div_factorial_le_exp ‖r h‖ (norm_nonneg (r h)) n)) (norm_nonneg _)

/-- The half-strength Gaussian bound makes every full-Gaussian directional moment integrable. -/
theorem integrable_gaussian_moment (hp : Measurable p) (hF : Measurable F)
    (hthin : Integrable (fun h => (Real.exp (-‖p h‖ ^ 2 / 2) : ℂ) * F h) ν)
    (L : E →L[ℝ] ℝ) (n : ℕ) :
    Integrable (fun h => (L (p h) : ℂ) ^ n * ((Real.exp (-‖p h‖ ^ 2) : ℂ) * F h)) ν := by
  have hLp : Measurable (fun h => L (p h)) := L.continuous.measurable.comp hp
  exact integrable_moment hLp (by fun_prop) (integrable_exp_times_gaussian hp hF hthin L) n

private theorem integral_exp_eq_zero_of_moments {r : H → ℝ} {w : H → ℂ}
    (hr : Measurable r) (hw : Measurable w)
    (hbound : Integrable (fun h => Real.exp ‖r h‖ * ‖w h‖) ν)
    (hm : ∀ n : ℕ, (∫ h, (r h : ℂ) ^ n * w h ∂ν) = 0) :
    (∫ h, Complex.exp ((r h : ℂ) * I) * w h ∂ν) = 0 := by
  let T (n : ℕ) (h : H) : ℂ := (((r h : ℂ) * I) ^ n / n.factorial) * w h
  have hsNorm (h : H) : HasSum (fun n => ‖T n h‖) (Real.exp ‖r h‖ * ‖w h‖) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa only [T, norm_mul, norm_div, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Complex.norm_I, mul_one] using
      (NormedSpace.expSeries_div_hasSum_exp ‖r h‖).mul_right ‖w h‖
  have htMeas (n : ℕ) : AEStronglyMeasurable (T n) ν := by
    dsimp only [T]
    fun_prop
  have htBound : Integrable (fun h => ∑' n, ‖T n h‖) ν :=
    hbound.congr (Filter.Eventually.of_forall fun h => (hsNorm h).tsum_eq.symm)
  have hs := hasSum_integral_of_dominated_convergence (fun n h => ‖T n h‖) htMeas
    (fun _ => Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall fun h => (hsNorm h).summable) htBound
    (f := fun h => Complex.exp ((r h : ℂ) * I) * w h)
    (Filter.Eventually.of_forall fun h => by
      rw [Complex.exp_eq_exp_ℂ]
      exact (NormedSpace.expSeries_div_hasSum_exp ((r h : ℂ) * I)).mul_right (w h))
  have hz (n : ℕ) : (∫ h, T n h ∂ν) = 0 := by
    have heq (h : H) : T n h = (I ^ n / n.factorial) * ((r h : ℂ) ^ n * w h) := by
      dsimp only [T]
      rw [mul_pow, mul_div_assoc]
      ring
    simp_rw [heq, integral_const_mul, hm, mul_zero]
  simpa only [hz, tsum_zero] using hs.tsum_eq.symm

private def positivePush (ν : Measure H) (p : H → E) (w : H → ℝ) : Measure E :=
  (ν.withDensity fun h => ENNReal.ofReal (w h)).map p

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] in
private theorem integral_positivePush (hp : Measurable p) {w : H → ℝ} (hw : Measurable w)
    {g : E → ℂ} (hg : Measurable g) :
    (∫ x, g x ∂positivePush ν p w) = ∫ h, g (p h) * (max (w h) 0 : ℝ) ∂ν := by
  rw [positivePush, integral_map hp.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', Complex.real_smul, mul_comm]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] in
private theorem integral_eq_sub_positivePush (hp : Measurable p) {w : H → ℝ}
    (hw : Measurable w) {g : E → ℂ} (hg : Measurable g)
    (hint : Integrable (fun h => g (p h) * (w h : ℂ)) ν) :
    (∫ h, g (p h) * (w h : ℂ) ∂ν) =
      (∫ x, g x ∂positivePush ν p w) - (∫ x, g x ∂positivePush ν p (fun h => -w h)) := by
  have hmono (v : H → ℝ) (hv : Measurable v) (hle : ∀ h, v h ≤ |w h|) :
      Integrable (fun h => g (p h) * (max (v h) 0 : ℝ)) ν := by
    refine hint.mono (by fun_prop) (Filter.Eventually.of_forall fun h => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (v h) (0 : ℝ))]
    exact mul_le_mul_of_nonneg_left (max_le (hle h) (abs_nonneg _)) (norm_nonneg _)
  have hneg : Measurable (fun h => -w h) := by fun_prop
  rw [integral_positivePush hp hw hg, integral_positivePush hp hneg hg,
    ← integral_sub (hmono w hw fun _ => le_abs_self _)
      (hmono (fun h => -w h) hneg fun _ => neg_le_abs _)]
  simp only [← mul_sub, ← ofReal_sub, max_zero_sub_max_neg_zero_eq_self]

private theorem integral_eq_zero_of_charIntegrals [CompleteSpace E] [SecondCountableTopology E]
    (hp : Measurable p) {w : H → ℝ} (hw : Measurable w) (hwint : Integrable w ν)
    (hchar : ∀ L : E →L[ℝ] ℝ,
      (∫ h, Complex.exp ((L (p h) : ℂ) * I) * (w h : ℂ) ∂ν) = 0)
    {g : E → ℂ} (hg : Measurable g)
    (hint : Integrable (fun h => g (p h) * (w h : ℂ)) ν) :
    (∫ h, g (p h) * (w h : ℂ) ∂ν) = 0 := by
  have hfin (v : H → ℝ) (hv : Integrable v ν) : IsFiniteMeasure (positivePush ν p v) := by
    have := isFiniteMeasure_withDensity_ofReal hv.2
    unfold positivePush
    infer_instance
  have := hfin w hwint
  have := hfin (fun h => -w h) hwint.neg
  have heq : positivePush ν p w = positivePush ν p (fun h => -w h) := by
    apply Measure.ext_of_charFunDual
    funext L
    simp only [charFunDual_apply]
    have hL : Measurable (fun x => Complex.exp ((L x : ℂ) * I)) := by fun_prop
    have hi : Integrable (fun h => Complex.exp ((L (p h) : ℂ) * I) * (w h : ℂ)) ν := by
      refine hwint.mono (by fun_prop) (Filter.Eventually.of_forall fun h => ?_)
      simp [mul_comm (L (p h) : ℂ) I, Complex.norm_exp_I_mul_ofReal]
    exact sub_eq_zero.mp ((integral_eq_sub_positivePush hp hw hL hi).symm.trans (hchar L))
  rw [integral_eq_sub_positivePush hp hw hg hint, heq, sub_self]

private theorem integral_test_eq_zero_of_exp_moments [CompleteSpace E] [SecondCountableTopology E]
    (hp : Measurable p) {w : H → ℂ} (hw : Measurable w)
    (hbound : ∀ L : E →L[ℝ] ℝ, Integrable (fun h => Real.exp ‖L (p h)‖ * ‖w h‖) ν)
    (hm : ∀ (L : E →L[ℝ] ℝ) (n : ℕ), (∫ h, (L (p h) : ℂ) ^ n * w h ∂ν) = 0)
    {g : E → ℂ} (hg : Measurable g) (hint : Integrable (fun h => g (p h) * w h) ν) :
    (∫ h, g (p h) * w h ∂ν) = 0 := by
  have hwint : Integrable w ν := (integrable_norm_iff hw.aestronglyMeasurable).mp (by
    simpa using hbound 0)
  have hgint (c : ℂ →L[ℝ] ℝ) (hc : ∀ z, ‖c z‖ ≤ ‖z‖) :
      Integrable (fun h => g (p h) * (c (w h) : ℂ)) ν := by
    refine hint.mono (by fun_prop) (Filter.Eventually.of_forall fun h => ?_)
    simp only [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hc _) (norm_nonneg _)
  have hreal (c : ℂ →L[ℝ] ℝ) (hc : ∀ z, ‖c z‖ ≤ ‖z‖) :
      (∫ h, g (p h) * (c (w h) : ℂ) ∂ν) = 0 := by
    have hcw : Measurable (fun h => c (w h)) := c.continuous.measurable.comp hw
    have hcwint : Integrable (fun h => c (w h)) ν :=
      hwint.mono hcw.aestronglyMeasurable (Filter.Eventually.of_forall fun h => hc (w h))
    refine integral_eq_zero_of_charIntegrals hp hcw hcwint (fun L => ?_) hg (hgint c hc)
    have hLp : Measurable (fun h => L (p h)) := L.continuous.measurable.comp hp
    have hcBound : Integrable (fun h => Real.exp ‖L (p h)‖ * ‖(c (w h) : ℂ)‖) ν := by
      refine (hbound L).mono' (by fun_prop) (Filter.Eventually.of_forall fun h => ?_)
      rw [Real.norm_of_nonneg (by positivity), Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hc _) (Real.exp_pos _).le
    refine integral_exp_eq_zero_of_moments hLp (by fun_prop) hcBound (fun n => ?_)
    have hm' := c.integral_comp_comm (integrable_moment hLp hw (hbound L) n)
    rw [hm L n, map_zero] at hm'
    have heq (h : H) : (L (p h) : ℂ) ^ n * (c (w h) : ℂ) =
        (c ((L (p h) : ℂ) ^ n * w h) : ℂ) := by
      simp only [← Complex.ofReal_pow, ← Complex.real_smul, map_smul]
      rw [smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
    simpa only [heq, integral_complex_ofReal, ofReal_zero] using congrArg Complex.ofReal hm'
  have hr : ∀ z : ℂ, ‖Complex.reCLM z‖ ≤ ‖z‖ := Complex.abs_re_le_norm
  have hi : ∀ z : ℂ, ‖Complex.imCLM z‖ ≤ ‖z‖ := Complex.abs_im_le_norm
  have hsplit (h : H) : g (p h) * w h =
      g (p h) * (Complex.reCLM (w h) : ℂ) + (g (p h) * (Complex.imCLM (w h) : ℂ)) * I := by
    simp only [Complex.reCLM_apply, Complex.imCLM_apply]
    conv_lhs => rw [← Complex.re_add_im (w h)]
    ring
  rw [show (fun h => g (p h) * w h) = _ from funext hsplit,
    integral_add (hgint Complex.reCLM hr) ((hgint Complex.imCLM hi).mul_const I),
    integral_mul_const, hreal Complex.reCLM hr, hreal Complex.imCLM hi, zero_mul, add_zero]

/-- Gaussian-weighted directional moments determine the integral against every integrable
measurable pullback test, without the Gaussian in the test integral. -/
theorem integral_eq_zero_of_gaussian_moments [FiniteDimensional ℝ E]
    (hp : Measurable p) (hF : Measurable F)
    (hthin : Integrable (fun h => (Real.exp (-‖p h‖ ^ 2 / 2) : ℂ) * F h) ν)
    (hm : ∀ (L : E →L[ℝ] ℝ) (n : ℕ),
      (∫ h, (L (p h) : ℂ) ^ n * ((Real.exp (-‖p h‖ ^ 2) : ℂ) * F h) ∂ν) = 0)
    {g : E → ℂ} (hg : Measurable g) (hint : Integrable (fun h => g (p h) * F h) ν) :
    (∫ h, g (p h) * F h ∂ν) = 0 := by
  let w (h : H) : ℂ := (Real.exp (-‖p h‖ ^ 2) : ℂ) * F h
  let g' (x : E) : ℂ := (Real.exp (‖x‖ ^ 2) : ℂ) * g x
  have hw : Measurable w := by dsimp only [w]; fun_prop
  have hg' : Measurable g' := by dsimp only [g']; fun_prop
  have hcancel (h : H) : g' (p h) * w h = g (p h) * F h := by
    dsimp only [g', w]
    rw [mul_mul_mul_comm, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]
  have hint' : Integrable (fun h => g' (p h) * w h) ν :=
    hint.congr (Filter.Eventually.of_forall fun h => (hcancel h).symm)
  simpa only [hcancel] using
    integral_test_eq_zero_of_exp_moments hp hw (integrable_exp_times_gaussian hp hF hthin)
      hm hg' hint'

omit [NormedSpace ℝ E] [BorelSpace E] in
/-- A bounded measurable test of compact support is integrable after pullback and multiplication
by a weight that is integrable with the half-strength Gaussian. -/
theorem integrable_mul_of_hasCompactSupport (hp : Measurable p) (hF : Measurable F)
    (hthin : Integrable (fun h => (Real.exp (-‖p h‖ ^ 2 / 2) : ℂ) * F h) ν)
    {g : E → ℂ} (hg : Measurable g) (hgc : HasCompactSupport g)
    (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) : Integrable (fun h => g (p h) * F h) ν := by
  obtain ⟨R, hR⟩ := IsCompact.exists_bound_of_continuousOn hgc continuousOn_id
  obtain ⟨C, hC⟩ := hgb
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine (hthin.norm.const_mul (C * Real.exp (R ^ 2 / 2))).mono' (by fun_prop) <|
    Filter.Eventually.of_forall fun h => ?_
  have hb : ‖g (p h)‖ ≤ C * Real.exp (R ^ 2 / 2) * Real.exp (-‖p h‖ ^ 2 / 2) := by
    by_cases hz : g (p h) = 0
    · rw [hz, norm_zero]
      positivity
    have hr : ‖p h‖ ≤ R := hR _ (subset_closure hz)
    rw [mul_assoc, ← Real.exp_add]
    calc
      ‖g (p h)‖ ≤ C := hC _
      _ = C * 1 := (mul_one _).symm
      _ ≤ C * Real.exp (R ^ 2 / 2 + -‖p h‖ ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (Real.one_le_exp ?_) hC₀
        nlinarith only [hr, norm_nonneg (p h)]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- Vanishing full-Gaussian moments and integrability with the half-strength Gaussian imply
vanishing of every integrable pulled-back test against the original weight. -/
def GaussianWeightedMomentDeterminationStatement : Prop :=
  ∀ (H E : Type*) [MeasurableSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure H) (p : H → E) (F : H → ℂ),
    Measurable p → Measurable F →
    Integrable (fun h => (Real.exp (-‖p h‖ ^ 2 / 2) : ℂ) * F h) ν →
    (∀ (L : E →L[ℝ] ℝ) (n : ℕ),
      (∫ h, (L (p h) : ℂ) ^ n * ((Real.exp (-‖p h‖ ^ 2) : ℂ) * F h) ∂ν) = 0) →
    ∀ g : E → ℂ, Measurable g → Integrable (fun h => g (p h) * F h) ν →
      (∫ h, g (p h) * F h ∂ν) = 0

theorem gaussianWeightedMomentDetermination : GaussianWeightedMomentDeterminationStatement := by
  intro H E _ _ _ _ _ _ ν p F hp hF hthin hm g hg hint
  exact integral_eq_zero_of_gaussian_moments hp hF hthin hm hg hint

end Langlands.Analysis.GaussianWeightedMoment
