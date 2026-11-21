import Langlands.Global.RankinSelberg.ArchimedeanMellinPair
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mellin convolution in logarithmic coordinates

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology Real

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinConvolution

open ArchimedeanMellinPair

/-- The integrand for Mellin convolution with one distinguished function `h₀`. -/
def mconvIntegrand {m : ℕ} (ε : ℝ) (h₀ : ℝ → ℂ) (h : Fin m → ℝ → ℂ) (t : ℝ)
    (τ : Fin m → ℝ) : ℂ :=
  h₀ (t * Real.exp (-(ε * ∑ j, τ j))) * ∏ j, h j (Real.exp (ε * τ j))

/-- `mconv ε h₀ h t = ∫_{τ ∈ ℝ^m} h₀(t e^(-ε Σ τ_j)) ∏_j h_j(e^(ε τ_j)) dτ`. For `ε = 1` this
is the multiplicative convolution of `h₀` and the `m` functions in `h` on `(0, ∞)`;
for `ε = -1` it is the same convolution written with the opposite parametrization. -/
def mconv {m : ℕ} (ε : ℝ) (h₀ : ℝ → ℂ) (h : Fin m → ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ τ, mconvIntegrand ε h₀ h t τ

/-- For a rapidly decreasing `g` and `ε ≠ 0`, `τ ↦ e^(p τ) ‖g(e^(ε τ))‖` is integrable on `ℝ`. -/
theorem integrable_exp_mul_norm_comp_exp {g : ℝ → ℂ} (hg : Measurable g) (hdec : RapidDecay g)
    {ε : ℝ} (hε : ε ≠ 0) (p : ℝ) :
    Integrable (fun τ : ℝ => Real.exp (p * τ) * ‖g (Real.exp (ε * τ))‖) := by
  obtain ⟨C1, hC1⟩ := hdec (-(p + 1) / ε)
  obtain ⟨C2, hC2⟩ := hdec ((1 - p) / ε)
  have hC1' := RapidDecay.nonneg_const hC1
  have hC2' := RapidDecay.nonneg_const hC2
  have hmeas : Measurable (fun τ : ℝ => Real.exp (p * τ) * ‖g (Real.exp (ε * τ))‖) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (hg.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))).norm
  have hbase : Integrable (fun τ : ℝ => Real.exp (-|τ|)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    apply IntegrableOn.union
    · refine (integrableOn_exp_Iic 0).congr_fun (fun t ht => ?_) measurableSet_Iic
      rw [abs_of_nonpos ht, neg_neg]
    · refine (integrableOn_exp_neg_Ioi 0).congr_fun (fun t ht => ?_) measurableSet_Ioi
      dsimp only
      rw [abs_of_nonneg (mem_Ioi.1 ht).le]
  refine (hbase.const_mul (C1 + C2)).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  have hpos : ∀ q : ℝ, Real.exp (ε * τ) ^ q = Real.exp (ε * q * τ) := fun q => by
    rw [← Real.exp_mul]; ring_nf
  have h1 := hC1 _ (Real.exp_pos (ε * τ))
  have h2 := hC2 _ (Real.exp_pos (ε * τ))
  rw [hpos] at h1 h2
  have e1 : ε * (-(p + 1) / ε) * τ = -(p + 1) * τ := by field_simp
  have e2 : ε * ((1 - p) / ε) * τ = (1 - p) * τ := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb : Real.exp (p * τ) * ‖g (Real.exp (ε * τ))‖ ≤ (C1 + C2) * Real.exp (-|τ|) := by
    rcases le_total 0 τ with hτ | hτ
    · calc Real.exp (p * τ) * ‖g (Real.exp (ε * τ))‖
          ≤ Real.exp (p * τ) * (C1 * Real.exp (-(p + 1) * τ)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = C1 * Real.exp (-|τ|) := by
            rw [abs_of_nonneg hτ, mul_left_comm, ← Real.exp_add]; ring_nf
        _ ≤ (C1 + C2) * Real.exp (-|τ|) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    · calc Real.exp (p * τ) * ‖g (Real.exp (ε * τ))‖
          ≤ Real.exp (p * τ) * (C2 * Real.exp ((1 - p) * τ)) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = C2 * Real.exp (-|τ|) := by
            rw [abs_of_nonpos hτ, mul_left_comm, ← Real.exp_add]; ring_nf
        _ ≤ (C1 + C2) * Real.exp (-|τ|) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  exact hb

theorem measurable_mconvIntegrand {m : ℕ} (ε : ℝ) {h₀ : ℝ → ℂ} {h : Fin m → ℝ → ℂ}
    (hh₀ : Measurable h₀) (hh : ∀ j, Measurable (h j)) :
    Measurable (Function.uncurry (mconvIntegrand ε h₀ h)) := by
  refine (hh₀.comp (measurable_fst.mul (Real.measurable_exp.comp
    (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).comp measurable_snd)).neg))).mul ?_
  exact Finset.measurable_prod _ fun j _ => (hh j).comp (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)))

theorem measurable_mconv {m : ℕ} (ε : ℝ) {h₀ : ℝ → ℂ} {h : Fin m → ℝ → ℂ} (hh₀ : Measurable h₀)
    (hh : ∀ j, Measurable (h j)) : Measurable (mconv ε h₀ h) :=
  ((measurable_mconvIntegrand ε hh₀ hh).stronglyMeasurable.integral_prod_right'
    (ν := volume)).measurable

/-- A product bound for the convolution integrand. -/
theorem norm_mconvIntegrand_le {m : ℕ} (ε : ℝ) {h₀ : ℝ → ℂ} {h : Fin m → ℝ → ℂ} {C M : ℝ}
    (hC : ∀ t : ℝ, 0 < t → ‖h₀ t‖ ≤ C * t ^ M) {t : ℝ} (ht : 0 < t) (τ : Fin m → ℝ) :
    ‖mconvIntegrand ε h₀ h t τ‖ ≤ C * t ^ M *
      ∏ j, (Real.exp (-(ε * M) * τ j) * ‖h j (Real.exp (ε * τ j))‖) := by
  rw [mconvIntegrand, norm_mul, norm_prod]
  have h1 := hC _ (mul_pos ht (Real.exp_pos (-(ε * ∑ j, τ j))))
  rw [Real.mul_rpow ht.le (Real.exp_pos _).le, ← Real.exp_mul] at h1
  have hexp : Real.exp (-(ε * ∑ j, τ j) * M) = ∏ j, Real.exp (-(ε * M) * τ j) := by
    rw [← Real.exp_sum]; congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp] at h1
  calc ‖h₀ (t * Real.exp (-(ε * ∑ j, τ j)))‖ * ∏ j, ‖h j (Real.exp (ε * τ j))‖
      ≤ C * (t ^ M * ∏ j, Real.exp (-(ε * M) * τ j)) * ∏ j, ‖h j (Real.exp (ε * τ j))‖ :=
        mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun j _ => norm_nonneg _)
    _ = C * t ^ M * ∏ j, (Real.exp (-(ε * M) * τ j) * ‖h j (Real.exp (ε * τ j))‖) := by
        rw [Finset.prod_mul_distrib]; ring

theorem integrable_mconvIntegrand {m : ℕ} {ε : ℝ} (hε : ε ≠ 0) {h₀ : ℝ → ℂ}
    {h : Fin m → ℝ → ℂ} (hh₀ : Measurable h₀) (hh : ∀ j, Measurable (h j))
    (hd₀ : RapidDecay h₀) (hd : ∀ j, RapidDecay (h j)) {t : ℝ} (ht : 0 < t) :
    Integrable (mconvIntegrand ε h₀ h t) := by
  obtain ⟨C, hC⟩ := hd₀ 0
  have hint : ∀ j, Integrable (fun τ : ℝ => Real.exp (-(ε * 0) * τ) * ‖h j (Real.exp (ε * τ))‖) :=
    fun j => integrable_exp_mul_norm_comp_exp (hh j) (hd j) hε _
  refine ((Integrable.fintype_prod (μ := fun _ => volume) hint).const_mul (C * t ^ (0 : ℝ))).mono' ?_
    (ae_of_all _ fun τ => norm_mconvIntegrand_le ε hC ht τ)
  exact ((measurable_mconvIntegrand ε hh₀ hh).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- The same bound applies to the integral of the absolute value. -/
theorem integral_norm_mconvIntegrand_le {m : ℕ} {ε : ℝ} (hε : ε ≠ 0) {h₀ : ℝ → ℂ}
    {h : Fin m → ℝ → ℂ} (hh : ∀ j, Measurable (h j)) (hdec : ∀ j, RapidDecay (h j)) {C M : ℝ}
    (hC : ∀ t : ℝ, 0 < t → ‖h₀ t‖ ≤ C * t ^ M) {t : ℝ} (ht : 0 < t) :
    (∫ τ, ‖mconvIntegrand ε h₀ h t τ‖) ≤ C * t ^ M *
      ∏ j, ∫ τ : ℝ, Real.exp (-(ε * M) * τ) * ‖h j (Real.exp (ε * τ))‖ := by
  have hint : ∀ j, Integrable (fun τ : ℝ => Real.exp (-(ε * M) * τ) * ‖h j (Real.exp (ε * τ))‖) :=
    fun j => integrable_exp_mul_norm_comp_exp (hh j) (hdec j) hε _
  rw [← integral_fintype_prod_volume_eq_prod, ← integral_const_mul]
  exact integral_mono_of_nonneg (ae_of_all _ fun τ => norm_nonneg _)
    ((Integrable.fintype_prod (μ := fun _ => volume) hint).const_mul _)
    (ae_of_all _ fun τ => norm_mconvIntegrand_le ε hC ht τ)

theorem rapidDecay_mconv {m : ℕ} {ε : ℝ} (hε : ε ≠ 0) {h₀ : ℝ → ℂ} {h : Fin m → ℝ → ℂ}
    (hdec₀ : RapidDecay h₀) (hh : ∀ j, Measurable (h j)) (hdec : ∀ j, RapidDecay (h j)) :
    RapidDecay (mconv ε h₀ h) := by
  intro M
  obtain ⟨C, hC⟩ := hdec₀ M
  refine ⟨C * ∏ j, ∫ τ : ℝ, Real.exp (-(ε * M) * τ) * ‖h j (Real.exp (ε * τ))‖,
    fun t ht => ?_⟩
  calc ‖mconv ε h₀ h t‖ ≤ ∫ τ, ‖mconvIntegrand ε h₀ h t τ‖ := norm_integral_le_integral_norm _
    _ ≤ _ := integral_norm_mconvIntegrand_le hε hh hdec hC ht
    _ = _ := by ring

/-- The Mellin integral in the substitution `t = exp τ`. -/
theorem mellin_eq_log_integral (g : ℝ → ℂ) (s : ℂ) :
    mellin g s = ∫ τ : ℝ, Complex.exp ((τ : ℂ) * s) * g (Real.exp τ) := by
  rw [mellin, ← integral_comp_exp]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [Complex.real_smul, smul_eq_mul]
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 (Real.exp_ne_zero τ)),
    ← Complex.ofReal_log (Real.exp_pos τ).le, Real.log_exp, ← mul_assoc, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 2
  ring

/-- Reversing all logarithmic coordinates leaves the integral unchanged. -/
theorem mconv_neg {m : ℕ} (ε : ℝ) (h₀ : ℝ → ℂ) (h : Fin m → ℝ → ℂ) (t : ℝ) :
    mconv (-ε) h₀ h t = mconv ε h₀ h t := by
  rw [mconv, mconv, ← integral_neg_eq_self (mconvIntegrand ε h₀ h t) volume]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp [mconvIntegrand, Pi.neg_apply, Finset.sum_neg_distrib, mul_neg, neg_mul]

/-- Mellin transforms turn the convolution (with `ε = 1`) into a product. -/
theorem mellin_mconv {m : ℕ} {h₀ : ℝ → ℂ} {h : Fin m → ℝ → ℂ} (hh₀ : Measurable h₀)
    (hh : ∀ j, Measurable (h j)) (hd₀ : RapidDecay h₀) (hd : ∀ j, RapidDecay (h j)) (s : ℂ) :
    mellin (mconv 1 h₀ h) s = mellin h₀ s * ∏ j, mellin (h j) s := by
  let F : (Fin m → ℝ) → ℂ := fun τ => ∏ j, h j (Real.exp (τ j))
  let δ : (Fin m → ℝ) → ℝ := fun τ => Real.exp (-∑ j, τ j)
  have hF : Measurable F := Finset.measurable_prod _ fun j _ =>
    (hh j).comp (Real.measurable_exp.comp (measurable_pi_apply j))
  have hδ : Measurable δ := Real.measurable_exp.comp
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).neg
  have hId : mconv 1 h₀ h = theta volume F δ h₀ := by
    funext t
    simp [mconv, mconvIntegrand, theta, F, δ, mul_comm]
  have hnorm : ∀ τ : Fin m → ℝ, ‖F τ‖ * δ τ ^ (-s).re =
      ∏ j, (Real.exp (s.re * τ j) * ‖h j (Real.exp (τ j))‖) := by
    intro τ
    dsimp only [F, δ]
    rw [norm_prod, ← Real.exp_mul, neg_re, neg_mul_neg, Finset.prod_mul_distrib, ← Real.exp_sum,
      ← Finset.mul_sum, mul_comm s.re]
    exact mul_comm _ _
  have hI : Integrable (fun τ : Fin m → ℝ => ‖F τ‖ * δ τ ^ (-s).re) := by
    refine (Integrable.fintype_prod (μ := fun _ => volume) (f := fun j τ =>
      Real.exp (s.re * τ) * ‖h j (Real.exp τ)‖) (fun j => ?_)).congr
      (ae_of_all _ fun τ => (hnorm τ).symm)
    simpa only [one_mul] using integrable_exp_mul_norm_comp_exp (hh j) (hd j) (ε := 1) one_ne_zero s.re
  rw [hId, ← neg_neg s, mellin_theta volume F δ hF.aestronglyMeasurable hδ
    (fun τ => Real.exp_pos _) h₀ hh₀ hd₀ (-s) hI, neg_neg s, mul_comm (mellin h₀ s)]
  congr 1
  simp_rw [mellin_eq_log_integral]
  rw [← integral_fintype_prod_volume_eq_prod]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  dsimp only [F, δ]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, cpow_def_of_ne_zero (ofReal_ne_zero.2 (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg, Complex.ofReal_sum,
    neg_mul_neg, Finset.sum_mul]
  ring

/-! ### Integrating over the scalings of fixed product -/

/-- The logarithmic parametrization of the independent scales with product `a`. -/
def scale {m : ℕ} (ε a : ℝ) (τ : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cons (a * Real.exp (-(ε * ∑ j, τ j))) (fun j => Real.exp (ε * τ j))

@[simp] theorem scale_zero {m : ℕ} (ε a : ℝ) (τ : Fin m → ℝ) :
    scale ε a τ 0 = a * Real.exp (-(ε * ∑ j, τ j)) := Fin.cons_zero _ _

@[simp] theorem scale_succ {m : ℕ} (ε a : ℝ) (τ : Fin m → ℝ) (j : Fin m) :
    scale ε a τ j.succ = Real.exp (ε * τ j) := Fin.cons_succ _ _ j

private theorem exp_mul_sum {m : ℕ} (ε : ℝ) (τ : Fin m → ℝ) :
    Real.exp (ε * ∑ j, τ j) = ∏ j, Real.exp (ε * τ j) := by
  rw [Finset.mul_sum, Real.exp_sum]

theorem scale_pos {m : ℕ} (ε : ℝ) {a : ℝ} (ha : 0 < a) (τ : Fin m → ℝ) (i : Fin (m + 1)) :
    0 < scale ε a τ i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [scale_zero]; positivity
  · rw [scale_succ]; positivity

theorem measurable_scale {m : ℕ} (ε a : ℝ) (i : Fin (m + 1)) :
    Measurable (fun τ : Fin m → ℝ => scale ε a τ i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [scale_zero]
    exact measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)).neg)
  · simp only [scale_succ]
    exact Real.measurable_exp.comp (measurable_const.mul (measurable_pi_apply j))

theorem prod_scale {m : ℕ} (ε a : ℝ) (τ : Fin m → ℝ) : ∏ i, scale ε a τ i = a := by
  rw [Fin.prod_univ_succ, scale_zero]
  simp only [scale_succ]
  rw [← exp_mul_sum, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

theorem scale_inv {m : ℕ} (ε a : ℝ) (τ : Fin m → ℝ) (i : Fin (m + 1)) :
    (scale ε a τ i)⁻¹ = scale (-ε) a⁻¹ τ i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [scale_zero, neg_mul, neg_neg, mul_inv_rev, ← Real.exp_neg]
    exact mul_comm _ _
  · simp only [scale_succ, neg_mul, Real.exp_neg]

/-- Translating the logarithmic coordinates moves the individual `δᵢ` into their product. -/
theorem prod_scaled_eq {m : ℕ} {ε : ℝ} (hε : ε ≠ 0) (a : ℝ) (τ : Fin m → ℝ)
    (h : Fin (m + 1) → ℝ → ℂ) (δ : Fin (m + 1) → ℝ) (hδ : ∀ i, 0 < δ i) :
    (∏ i, h i (scale ε a τ i * δ i)) =
      mconvIntegrand ε (h 0) (fun j => h j.succ) (a * ∏ i, δ i)
        (τ + fun j => Real.log (δ j.succ) / ε) := by
  let σ : Fin m → ℝ := τ + fun j => Real.log (δ j.succ) / ε
  have he (j : Fin m) : Real.exp (ε * σ j) = Real.exp (ε * τ j) * δ j.succ := by
    dsimp only [σ, Pi.add_apply]
    rw [mul_add, Real.exp_add]
    have hcancel : ε * (Real.log (δ j.succ) / ε) = Real.log (δ j.succ) := by field_simp
    rw [hcancel, Real.exp_log (hδ _)]
  change _ = mconvIntegrand ε (h 0) (fun j => h j.succ) (a * ∏ i, δ i) σ
  rw [Fin.prod_univ_succ, mconvIntegrand, Fin.prod_univ_succ (f := δ)]
  simp only [scale_zero, scale_succ]
  refine congrArg₂ (· * ·) (congrArg (h 0) ?_)
    (Finset.prod_congr rfl fun j _ => congrArg (h j.succ) (he j).symm)
  rw [Real.exp_neg, Real.exp_neg, exp_mul_sum, exp_mul_sum]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  have hn : (∏ j : Fin m, δ j.succ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hδ _).ne'
  have hp : (∏ j : Fin m, Real.exp (ε * τ j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => Real.exp_ne_zero _
  field_simp

/-- With one integrable product weight, the theta integral of the convolution is obtained by
integrating the independent-scale theta integral over scales of product `a`. -/
theorem theta_mconv {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ] {m : ℕ}
    {F : X → ℂ} (hF : AEStronglyMeasurable F μ) {δ : Fin (m + 1) → X → ℝ}
    (hδm : ∀ i, Measurable (δ i)) (hδ : ∀ i x, 0 < δ i x) {h : Fin (m + 1) → ℝ → ℂ}
    (hh : ∀ i, Measurable (h i)) (hd : ∀ i, RapidDecay (h i)) {M : ℝ}
    (hM : Integrable (fun x => ‖F x‖ * (∏ i, δ i x) ^ M) μ)
    {ε a : ℝ} (hε : ε ≠ 0) (ha : 0 < a) :
    theta μ F (fun x => ∏ i, δ i x) (mconv ε (h 0) (fun j => h j.succ)) a =
      ∫ τ : Fin m → ℝ, ∫ x, F x * ∏ i, h i (scale ε a τ i * δ i x) ∂μ := by
  let g : X × (Fin m → ℝ) → ℂ := fun p => F p.1 * ∏ i, h i (scale ε a p.2 i * δ i p.1)
  have hgm : AEStronglyMeasurable g (μ.prod volume) := hF.comp_fst.mul
    (Finset.measurable_prod _ fun i _ => (hh i).comp (((measurable_scale ε a i).comp
      measurable_snd).mul ((hδm i).comp measurable_fst))).aestronglyMeasurable
  let t : X → ℝ := fun x => a * ∏ i, δ i x
  let σ : X → (Fin m → ℝ) := fun x j => Real.log (δ j.succ x) / ε
  let J : X → (Fin m → ℝ) → ℂ := fun x => mconvIntegrand ε (h 0) (fun j => h j.succ) (t x)
  have ht (x) : 0 < t x := mul_pos ha (Finset.prod_pos fun i _ => hδ i x)
  have hg (x) : (fun τ => g (x, τ)) = fun τ => F x * J x (τ + σ x) := by
    funext τ
    exact congrArg (F x * ·) (prod_scaled_eq hε a τ h (fun i => δ i x) (fun i => hδ i x))
  have hJ (x) : Integrable (J x) := integrable_mconvIntegrand hε (hh 0) (fun j => hh j.succ)
    (hd 0) (fun j => hd j.succ) (ht x)
  obtain ⟨C, hC⟩ := hd 0 M
  let D : ℝ := ∏ j : Fin m, ∫ r : ℝ, Real.exp (-(ε * M) * r) * ‖h j.succ (Real.exp (ε * r))‖
  have hgi : Integrable g (μ.prod volume) := by
    apply (integrable_prod_iff hgm).2
    refine ⟨ae_of_all _ fun x => ?_, ?_⟩
    · rw [hg x]
      exact ((hJ x).comp_add_right (σ x)).const_mul (F x)
    · refine (hM.const_mul (C * a ^ M * D)).mono' hgm.norm.integral_prod_right' ?_
      refine ae_of_all _ fun x => ?_
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      change (∫ τ, ‖(fun z => g (x, z)) τ‖) ≤ _
      rw [hg x]
      simp only [norm_mul, integral_const_mul]
      rw [integral_add_right_eq_self (fun z => ‖J x z‖) (σ x)]
      calc ‖F x‖ * (∫ τ, ‖J x τ‖) ≤ ‖F x‖ * (C * t x ^ M * D) :=
             mul_le_mul_of_nonneg_left (integral_norm_mconvIntegrand_le hε
               (fun j => hh j.succ) (fun j => hd j.succ) hC (ht x)) (norm_nonneg _)
        _ = _ := by
          dsimp only [t]
          rw [Real.mul_rpow ha.le (Finset.prod_nonneg fun i _ => (hδ i x).le)]
          ring
  rw [← integral_integral_swap (f := fun x τ => g (x, τ)) hgi]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change F x * (∫ τ, J x τ) = ∫ τ, g (x, τ)
  rw [hg x, integral_const_mul, integral_add_right_eq_self (J x) (σ x)]

end Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinConvolution

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanMellinConvolution ArchimedeanMellinPair

universe u

/-- Multiplicative convolution of a nonempty list of measurable rapidly decreasing functions,
and the Fubini identity relating its theta integral to the coordinatewise scales. -/
def ArchimedeanMellinConvolutionStatement : Prop :=
  (∀ (m : ℕ) (h : Fin (m + 1) → ℝ → ℂ), (∀ i, Measurable (h i)) → (∀ i, RapidDecay (h i)) →
    let H := mconv 1 (h 0) (fun j => h j.succ)
    Measurable H ∧ RapidDecay H ∧ ∀ s : ℂ, mellin H s = ∏ i, mellin (h i) s) ∧
  (∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [SFinite μ] (m : ℕ)
    (F : X → ℂ) (δ : Fin (m + 1) → X → ℝ) (h : Fin (m + 1) → ℝ → ℂ) (M ε a : ℝ),
    AEStronglyMeasurable F μ → (∀ i, Measurable (δ i)) → (∀ i x, 0 < δ i x) →
    (∀ i, Measurable (h i)) → (∀ i, RapidDecay (h i)) →
    Integrable (fun x => ‖F x‖ * (∏ i, δ i x) ^ M) μ → ε ≠ 0 → 0 < a →
      theta μ F (fun x => ∏ i, δ i x) (mconv ε (h 0) (fun j => h j.succ)) a =
        ∫ τ : Fin m → ℝ, ∫ x, F x * ∏ i, h i (scale ε a τ i * δ i x) ∂μ)

theorem archimedeanMellinConvolution : ArchimedeanMellinConvolutionStatement.{u} := by
  refine ⟨fun m h hm hd => ⟨measurable_mconv 1 (hm 0) (fun j => hm j.succ),
    rapidDecay_mconv one_ne_zero (hd 0) (fun j => hm j.succ) (fun j => hd j.succ),
    fun s => ?_⟩, ?_⟩
  · rw [Fin.prod_univ_succ]
    exact mellin_mconv (hm 0) (fun j => hm j.succ) (hd 0) (fun j => hd j.succ) s
  · intro X _ μ _ m F δ h M ε a hF hδm hδ hh hd hM hε ha
    exact theta_mconv μ hF hδm hδ hh hd hM hε ha

end Langlands.Global.RankinSelbergGlobal
