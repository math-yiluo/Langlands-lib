import Langlands.Representation.Archimedean.ComplexSwapJacquetAnalysis

/-!
# Weighted integration by parts on `ℂ`

Let `φ : ℂ → ℂ` be `C¹`, let `p(z) = z^i z̄^j`, and assume that `φ` and its derivatives
`Dφ(z) 1`, `Dφ(z) i`, `Dφ(z) z`, `Dφ(z)(i z)` are bounded by `C (1 + |z|)^(-a)` with
`i + j + 2 < a`. Then, for Lebesgue measure on `ℂ`,

* `integral_fderiv_mul_weight`: `∫ Dφ(z)(c) p(z) = -(i c ∫ φ z^(i-1) z̄^j + j c̄ ∫ φ z^i z̄^(j-1))`;
* `integral_fderiv_self_mul_weight`: `∫ Dφ(z)(z) p(z) = -(2 + i + j) ∫ φ p`;
* `integral_fderiv_I_mul_self_mul_weight`: `∫ Dφ(z)(i z) p(z) = -i (i - j) ∫ φ p`.

They come from `∫ Dψ(z)(c) = 0`, Euler's identity `∫ Dψ(z) z = -2 ∫ ψ` and
`∫ Dψ(z)(i z) = 0` for `ψ = φ p`, which are proved here for majorants `C (1 + |z|)^(-r)`
with `r > 2` (the `ComplexSwapJacquet` versions use `r = 3`).
-/

noncomputable section

open MeasureTheory Filter Topology Module Set

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexGLTwoMoment

/-! ## The majorant `(1 + |z|)^(-r)` -/

theorem integrable_one_add_norm_rpow {r : ℝ} (hr : 2 < r) :
    Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-r)) :=
  integrable_one_add_norm (E := ℂ) (μ := volume)
    (by rw [Complex.finrank_real_complex]; exact_mod_cast hr)

theorem nonneg_of_bound_rpow {φ : ℂ → ℂ} {C r : ℝ}
    (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-r)) : 0 ≤ C := by
  have h := hb 0
  simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

theorem integrable_of_bound_rpow {φ : ℂ → ℂ} (hφ : AEStronglyMeasurable φ) {C r : ℝ}
    (hr : 2 < r) (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-r)) : Integrable φ :=
  ((integrable_one_add_norm_rpow hr).const_mul C).mono' hφ (Eventually.of_forall hb)

theorem tendsto_cobounded_of_bound_rpow {φ : ℂ → ℂ} {C r : ℝ} (hr : 0 < r)
    (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-r)) :
    Tendsto φ (Bornology.cobounded ℂ) (𝓝 0) := by
  have h1 : Tendsto (fun z : ℂ => (1 + ‖z‖) ^ (-r)) (Bornology.cobounded ℂ) (𝓝 0) :=
    (tendsto_rpow_neg_atTop hr).comp
      (tendsto_atTop_add_const_left _ 1 tendsto_norm_cobounded_atTop)
  have h2 := h1.const_mul C
  rw [mul_zero] at h2
  exact squeeze_zero_norm hb h2

/-- `(1 + ρ x)^(-r) ≤ 2^r (1 + x)^(-r)` for `ρ ≥ 1/2`, `x ≥ 0` and `r ≥ 0`. -/
theorem one_add_mul_rpow_neg_le {ρ x r : ℝ} (hρ : 1 / 2 ≤ ρ) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    (1 + ρ * x) ^ (-r) ≤ 2 ^ r * (1 + x) ^ (-r) := by
  have h1 : 0 < (1 + x) * 2⁻¹ := by positivity
  have h2 : (1 + x) * 2⁻¹ ≤ 1 + ρ * x := by nlinarith
  calc (1 + ρ * x) ^ (-r) ≤ ((1 + x) * 2⁻¹) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)
    _ = 2 ^ r * (1 + x) ^ (-r) := by
        rw [Real.mul_rpow (by positivity) (by norm_num), Real.inv_rpow (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]

/-! ## Euler's identity and rotation invariance -/

/-- Euler's identity `∫ Dφ(z) z dz = -2 ∫ φ`, from `∫ φ(ρ z) dz = ρ⁻² ∫ φ`. -/
theorem integral_fderiv_apply_self_rpow {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) {C r : ℝ}
    (hr : 2 < r) (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-r))
    (hb' : ∀ z, ‖fderiv ℝ φ z z‖ ≤ C * (1 + ‖z‖) ^ (-r)) :
    ∫ z, fderiv ℝ φ z z = -2 * ∫ z, φ z := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hC : 0 ≤ C := nonneg_of_bound_rpow hb
  have hs : Metric.ball (1 : ℝ) (1 / 2) ∈ 𝓝 (1 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have hbound : ∀ z : ℂ, ∀ ρ ∈ Metric.ball (1 : ℝ) (1 / 2),
      ‖fderiv ℝ φ (ρ • z) z‖ ≤ 2 * 2 ^ r * C * (1 + ‖z‖) ^ (-r) := by
    intro z ρ hρ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hρ
    have hρ1 : 1 / 2 ≤ ρ := by linarith
    have hρ0 : 0 < ρ := by linarith
    have heq : fderiv ℝ φ (ρ • z) z = ρ⁻¹ • fderiv ℝ φ (ρ • z) (ρ • z) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ hρ0.ne', one_smul]
    have h1 := hb' (ρ • z)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ0] at h1
    have h2 := one_add_mul_rpow_neg_le hρ1 (norm_nonneg z) (by linarith : (0 : ℝ) ≤ r)
    have hρ2 : ρ⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ0]
    calc ρ⁻¹ * ‖fderiv ℝ φ (ρ • z) (ρ • z)‖ ≤ 2 * (C * (1 + ρ * ‖z‖) ^ (-r)) :=
          mul_le_mul hρ2 h1 (norm_nonneg _) (by norm_num)
      _ ≤ 2 * (C * (2 ^ r * (1 + ‖z‖) ^ (-r))) := by gcongr
      _ = 2 * 2 ^ r * C * (1 + ‖z‖) ^ (-r) := by ring
  have hderiv : ∀ z : ℂ, ∀ ρ ∈ Metric.ball (1 : ℝ) (1 / 2),
      HasDerivAt (fun ρ : ℝ => φ (ρ • z)) (fderiv ℝ φ (ρ • z) z) ρ := by
    intro z ρ _
    have h := (hd (ρ • z)).hasFDerivAt.comp_hasDerivAt ρ ((hasDerivAt_id ρ).smul_const z)
    rw [one_smul] at h
    exact h
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (ρ : ℝ) (z : ℂ) => φ (ρ • z))
    (F' := fun (ρ : ℝ) (z : ℂ) => fderiv ℝ φ (ρ • z) z)
    (bound := fun z => 2 * 2 ^ r * C * (1 + ‖z‖) ^ (-r)) hs
    (Eventually.of_forall fun ρ =>
      (hφ.continuous.comp (continuous_const_smul ρ)).aestronglyMeasurable)
    (by simpa using integrable_of_bound_rpow hφ.continuous.aestronglyMeasurable hr hb)
    (((hfc.comp (continuous_const_smul (1 : ℝ))).clm_apply continuous_id).aestronglyMeasurable)
    (Eventually.of_forall hbound)
    ((integrable_one_add_norm_rpow hr).const_mul (2 * 2 ^ r * C))
    (Eventually.of_forall hderiv)
  have hscale : (fun ρ : ℝ => ∫ z, φ (ρ • z)) =ᶠ[𝓝 (1 : ℝ)]
      fun ρ : ℝ => ((ρ ^ 2)⁻¹ : ℝ) • ∫ z, φ z := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with ρ hρ
    rw [Measure.integral_comp_smul_of_nonneg volume φ ρ (hR := le_of_lt hρ),
      Complex.finrank_real_complex]
  have hder2 : HasDerivAt (fun ρ : ℝ => ((ρ ^ 2)⁻¹ : ℝ) • ∫ z, φ z)
      ((-2 : ℝ) • ∫ z, φ z) 1 := by
    have h := ((hasDerivAt_pow 2 (1 : ℝ)).inv (by norm_num)).smul_const (∫ z, φ z)
    convert h using 2
    norm_num
  have huniq := hmain.2.unique (hder2.congr_of_eventuallyEq hscale)
  simp only [one_smul] at huniq
  rw [huniq, Complex.real_smul]
  push_cast
  ring

/-- `∫ Dφ(z) (i z) dz = 0`, from the rotation invariance `∫ φ(e^{iθ} z) dz = ∫ φ`. -/
theorem integral_fderiv_apply_I_mul_self_rpow {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) {C r : ℝ}
    (hr : 2 < r) (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-r))
    (hb' : ∀ z, ‖fderiv ℝ φ z (Complex.I * z)‖ ≤ C * (1 + ‖z‖) ^ (-r)) :
    ∫ z, fderiv ℝ φ z (Complex.I * z) = 0 := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hnorm : ∀ (θ : ℝ) (z : ℂ), ‖Complex.exp (θ * Complex.I) * z‖ = ‖z‖ := by
    intro θ z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hbound : ∀ z : ℂ, ∀ θ ∈ (Set.univ : Set ℝ),
      ‖fderiv ℝ φ (Complex.exp (θ * Complex.I) * z)
        (Complex.I * (Complex.exp (θ * Complex.I) * z))‖ ≤ C * (1 + ‖z‖) ^ (-r) := by
    intro z θ _
    have h := hb' (Complex.exp (θ * Complex.I) * z)
    rwa [hnorm] at h
  have hderiv : ∀ z : ℂ, ∀ θ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun θ : ℝ => φ (Complex.exp (θ * Complex.I) * z))
        (fderiv ℝ φ (Complex.exp (θ * Complex.I) * z)
          (Complex.I * (Complex.exp (θ * Complex.I) * z))) θ := by
    intro z θ _
    have hγ : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I) * z)
        (Complex.I * (Complex.exp (θ * Complex.I) * z)) θ := by
      have h := (((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp).mul_const z
      refine h.congr_deriv ?_
      simp only [id_eq]
      push_cast
      ring
    exact (hd _).hasFDerivAt.comp_hasDerivAt θ hγ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (x₀ := (0 : ℝ))
    (F := fun (θ : ℝ) (z : ℂ) => φ (Complex.exp (θ * Complex.I) * z))
    (F' := fun (θ : ℝ) (z : ℂ) => fderiv ℝ φ (Complex.exp (θ * Complex.I) * z)
      (Complex.I * (Complex.exp (θ * Complex.I) * z)))
    (bound := fun z => C * (1 + ‖z‖) ^ (-r)) Filter.univ_mem
    (Eventually.of_forall fun θ =>
      (hφ.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (by simpa using integrable_of_bound_rpow hφ.continuous.aestronglyMeasurable hr hb)
    (((hfc.comp (continuous_const.mul continuous_id)).clm_apply
      (continuous_const.mul (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall hbound)
    ((integrable_one_add_norm_rpow hr).const_mul C)
    (Eventually.of_forall hderiv)
  have hrot : (fun θ : ℝ => ∫ z, φ (Complex.exp (θ * Complex.I) * z)) =
      fun _ => ∫ z, φ z := by
    funext θ
    have hmp := (rotation (Circle.exp θ)).measurePreserving
    have hme := (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding
    have h := hmp.integral_comp hme φ
    simpa [rotation_apply, Circle.coe_exp] using h
  have huniq := hmain.2.unique (by rw [hrot]; exact hasDerivAt_const _ _)
  simpa using huniq

/-! ## The weight `z^i z̄^j` -/

/-- The weight `p(z) = z^i z̄^j`. -/
def weight (i j : ℕ) (z : ℂ) : ℂ :=
  z ^ i * (starRingEnd ℂ z) ^ j

/-- The real derivative of the weight: `Dp(z)(v) = i z^(i-1) v z̄^j + j z^i z̄^(j-1) v̄`. -/
def weightDeriv (i j : ℕ) (z v : ℂ) : ℂ :=
  (i : ℂ) * z ^ (i - 1) * v * (starRingEnd ℂ z) ^ j +
    (j : ℂ) * z ^ i * (starRingEnd ℂ z) ^ (j - 1) * starRingEnd ℂ v

theorem contDiff_weight (i j : ℕ) : ContDiff ℝ ⊤ (weight i j) := by
  unfold weight
  exact (contDiff_id.pow i).mul
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.pow j)

theorem hasFDerivAt_weight (i j : ℕ) (z : ℂ) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (weight i j) L z ∧ ∀ v, L v = weightDeriv i j z v := by
  have h1 : HasFDerivAt (fun w : ℂ => w ^ i)
      (((1 : ℂ →L[ℂ] ℂ).smulRight ((i : ℂ) * z ^ (i - 1))).restrictScalars ℝ) z :=
    (hasDerivAt_pow i z).hasFDerivAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun w : ℂ => starRingEnd ℂ w) (Complex.conjCLE : ℂ →L[ℝ] ℂ) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have h2 : HasFDerivAt (fun w : ℂ => (starRingEnd ℂ w) ^ j)
      ((((1 : ℂ →L[ℂ] ℂ).smulRight ((j : ℂ) * (starRingEnd ℂ z) ^ (j - 1))).restrictScalars
        ℝ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z :=
    ((hasDerivAt_pow j (starRingEnd ℂ z)).hasFDerivAt.restrictScalars ℝ).comp z hc
  refine ⟨_, h1.mul h2, fun v => ?_⟩
  simp only [weightDeriv]
  simp
  ring

theorem fderiv_weight_apply (i j : ℕ) (z v : ℂ) :
    fderiv ℝ (weight i j) z v = weightDeriv i j z v := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_weight i j z
  rw [hL.fderiv, hLv]

theorem norm_weight (i j : ℕ) (z : ℂ) : ‖weight i j z‖ = ‖z‖ ^ (i + j) := by
  simp [weight, norm_pow, pow_add]

theorem natCast_mul_pow_sub_one_mul (i : ℕ) (z : ℂ) :
    (i : ℂ) * z ^ (i - 1) * z = (i : ℂ) * z ^ i := by
  rcases i with _ | i
  · simp
  · simp [pow_succ, mul_assoc]

theorem weightDeriv_self (i j : ℕ) (z : ℂ) :
    weightDeriv i j z z = ((i + j : ℕ) : ℂ) * weight i j z := by
  unfold weightDeriv weight
  have h1 := natCast_mul_pow_sub_one_mul i z
  have h2 := natCast_mul_pow_sub_one_mul j (starRingEnd ℂ z)
  push_cast
  linear_combination (starRingEnd ℂ z) ^ j * h1 + z ^ i * h2

theorem weightDeriv_I_mul_self (i j : ℕ) (z : ℂ) :
    weightDeriv i j z (Complex.I * z) = Complex.I * ((i : ℂ) - (j : ℂ)) * weight i j z := by
  unfold weightDeriv weight
  have h1 := natCast_mul_pow_sub_one_mul i z
  have h2 := natCast_mul_pow_sub_one_mul j (starRingEnd ℂ z)
  simp only [map_mul, Complex.conj_I]
  linear_combination Complex.I * (starRingEnd ℂ z) ^ j * h1 - Complex.I * z ^ i * h2

/-- `|Dp(z)(v)| ≤ (i + j) |v| (1 + |z|)^(i + j)`. -/
theorem norm_weightDeriv_le (i j : ℕ) (z v : ℂ) :
    ‖weightDeriv i j z v‖ ≤ ((i + j : ℕ) : ℝ) * ‖v‖ * (1 + ‖z‖) ^ (i + j) := by
  have hz : ‖z‖ ≤ 1 + ‖z‖ := by linarith
  have h1 : ‖z‖ ^ (i - 1) * ‖z‖ ^ j ≤ (1 + ‖z‖) ^ (i + j) := by
    calc ‖z‖ ^ (i - 1) * ‖z‖ ^ j ≤ (1 + ‖z‖) ^ (i - 1) * (1 + ‖z‖) ^ j := by gcongr
      _ = (1 + ‖z‖) ^ (i - 1 + j) := by rw [pow_add]
      _ ≤ (1 + ‖z‖) ^ (i + j) :=
          pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by omega)
  have h2 : ‖z‖ ^ i * ‖z‖ ^ (j - 1) ≤ (1 + ‖z‖) ^ (i + j) := by
    calc ‖z‖ ^ i * ‖z‖ ^ (j - 1) ≤ (1 + ‖z‖) ^ i * (1 + ‖z‖) ^ (j - 1) := by gcongr
      _ = (1 + ‖z‖) ^ (i + (j - 1)) := by rw [pow_add]
      _ ≤ (1 + ‖z‖) ^ (i + j) :=
          pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by omega)
  unfold weightDeriv
  calc ‖(i : ℂ) * z ^ (i - 1) * v * (starRingEnd ℂ z) ^ j +
        (j : ℂ) * z ^ i * (starRingEnd ℂ z) ^ (j - 1) * starRingEnd ℂ v‖
      ≤ (i : ℝ) * (‖z‖ ^ (i - 1) * ‖z‖ ^ j) * ‖v‖ +
          (j : ℝ) * (‖z‖ ^ i * ‖z‖ ^ (j - 1)) * ‖v‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_conj]
        ring
    _ ≤ (i : ℝ) * (1 + ‖z‖) ^ (i + j) * ‖v‖ + (j : ℝ) * (1 + ‖z‖) ^ (i + j) * ‖v‖ := by
        gcongr
    _ = ((i + j : ℕ) : ℝ) * ‖v‖ * (1 + ‖z‖) ^ (i + j) := by
        push_cast
        ring

/-! ## Bounds for products with the weight -/

theorem mul_le_rpow_aux {x y C K a u : ℝ} {m : ℕ} (hu : 0 < u) (hx : 0 ≤ x)
    (hxb : x ≤ C * u ^ (-a)) (hy0 : 0 ≤ y) (hy : y ≤ K * u ^ m) :
    x * y ≤ C * K * u ^ (-(a - m)) := by
  calc x * y ≤ (C * u ^ (-a)) * (K * u ^ m) := mul_le_mul hxb hy hy0 (hx.trans hxb)
    _ = C * K * (u ^ (-a) * u ^ (m : ℝ)) := by rw [Real.rpow_natCast]; ring
    _ = C * K * u ^ (-(a - m)) := by
        rw [← Real.rpow_add hu]
        congr 2
        ring

theorem norm_weight_le {i j m : ℕ} (h : i + j ≤ m) (z : ℂ) :
    ‖weight i j z‖ ≤ 1 * (1 + ‖z‖) ^ m := by
  rw [norm_weight, one_mul]
  calc ‖z‖ ^ (i + j) ≤ (1 + ‖z‖) ^ (i + j) :=
        pow_le_pow_left₀ (norm_nonneg z) (by linarith) _
    _ ≤ (1 + ‖z‖) ^ m := pow_le_pow_right₀ (by linarith [norm_nonneg z]) h

theorem norm_mul_weight_le {φ : ℂ → ℂ} {C a : ℝ} (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-a))
    {i j m : ℕ} (h : i + j ≤ m) (z : ℂ) :
    ‖φ z * weight i j z‖ ≤ C * (1 + ‖z‖) ^ (-(a - m)) := by
  rw [norm_mul]
  have h := mul_le_rpow_aux (by positivity) (norm_nonneg _) (hb z) (norm_nonneg _)
    (norm_weight_le h z)
  rwa [mul_one] at h

theorem fderiv_mul_weight_apply {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ) (i j : ℕ) (z v : ℂ) :
    fderiv ℝ (fun z => φ z * weight i j z) z v =
      fderiv ℝ φ z v * weight i j z + φ z * weightDeriv i j z v := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_weight i j z
  have hm : HasFDerivAt (fun z => φ z * weight i j z)
      (φ z • L + weight i j z • fderiv ℝ φ z) z := (hφ z).hasFDerivAt.mul hL
  rw [hm.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hLv]
  ring

theorem contDiff_mul_weight {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (i j : ℕ) :
    ContDiff ℝ 1 fun z => φ z * weight i j z :=
  hφ.mul ((contDiff_weight i j).of_le le_top)

/-- The bound on `D(φ p)(z)(w z)` from bounds on `φ`, `Dφ(z)(w z)` and `Dp(z)(w z)`. -/
theorem norm_fderiv_mul_weight_le {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ) {C a : ℝ} (i j : ℕ)
    (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-a)) (w : ℂ → ℂ)
    (hw : ∀ z, ‖fderiv ℝ φ z (w z)‖ ≤ C * (1 + ‖z‖) ^ (-a))
    (hpw : ∀ z, ‖weightDeriv i j z (w z)‖ ≤ ((i + j : ℕ) : ℝ) * (1 + ‖z‖) ^ (i + j))
    (z : ℂ) :
    ‖fderiv ℝ (fun z => φ z * weight i j z) z (w z)‖ ≤
      C * (1 + ((i + j : ℕ) : ℝ)) * (1 + ‖z‖) ^ (-(a - ((i + j : ℕ) : ℝ))) := by
  rw [fderiv_mul_weight_apply hφ]
  have h1 := mul_le_rpow_aux (m := i + j) (by positivity) (norm_nonneg _) (hw z)
    (norm_nonneg _) (norm_weight_le le_rfl z)
  have h2 := mul_le_rpow_aux (m := i + j) (by positivity) (norm_nonneg _) (hb z)
    (norm_nonneg _) (hpw z)
  calc ‖fderiv ℝ φ z (w z) * weight i j z + φ z * weightDeriv i j z (w z)‖
      ≤ ‖fderiv ℝ φ z (w z)‖ * ‖weight i j z‖ + ‖φ z‖ * ‖weightDeriv i j z (w z)‖ := by
        rw [← norm_mul, ← norm_mul]
        exact norm_add_le _ _
    _ ≤ C * 1 * (1 + ‖z‖) ^ (-(a - ((i + j : ℕ) : ℝ))) +
          C * ((i + j : ℕ) : ℝ) * (1 + ‖z‖) ^ (-(a - ((i + j : ℕ) : ℝ))) := add_le_add h1 h2
    _ = C * (1 + ((i + j : ℕ) : ℝ)) * (1 + ‖z‖) ^ (-(a - ((i + j : ℕ) : ℝ))) := by ring

theorem norm_weightDeriv_const_le (i j : ℕ) {v : ℂ} (hv : ‖v‖ = 1) (z : ℂ) :
    ‖weightDeriv i j z v‖ ≤ ((i + j : ℕ) : ℝ) * (1 + ‖z‖) ^ (i + j) := by
  have h := norm_weightDeriv_le i j z v
  rwa [hv, mul_one] at h

theorem norm_weightDeriv_self_le (i j : ℕ) (z : ℂ) :
    ‖weightDeriv i j z z‖ ≤ ((i + j : ℕ) : ℝ) * (1 + ‖z‖) ^ (i + j) := by
  rw [weightDeriv_self, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_weight_le (le_refl (i + j)) z)
    (Nat.cast_nonneg _)

theorem norm_weightDeriv_I_mul_self_le (i j : ℕ) (z : ℂ) :
    ‖weightDeriv i j z (Complex.I * z)‖ ≤ ((i + j : ℕ) : ℝ) * (1 + ‖z‖) ^ (i + j) := by
  rw [weightDeriv_I_mul_self, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hij : ‖(i : ℂ) - (j : ℂ)‖ ≤ ((i + j : ℕ) : ℝ) := by
    calc ‖(i : ℂ) - (j : ℂ)‖ ≤ ‖(i : ℂ)‖ + ‖(j : ℂ)‖ := norm_sub_le _ _
      _ = ((i + j : ℕ) : ℝ) := by simp
  exact mul_le_mul hij (by simpa using norm_weight_le (le_refl (i + j)) z) (norm_nonneg _)
    (Nat.cast_nonneg _)

/-! ## Weighted integration by parts -/

section Weighted

variable {φ : ℂ → ℂ} {C a : ℝ} (i j : ℕ)

theorem integrable_mul_weight (hφ : Continuous φ) (ha : ((i + j : ℕ) : ℝ) + 2 < a)
    (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-a)) {i' j' : ℕ} (h : i' + j' ≤ i + j) :
    Integrable fun z => φ z * weight i' j' z :=
  integrable_of_bound_rpow
    (hφ.mul (contDiff_weight i' j').continuous).aestronglyMeasurable
    (by linarith) (norm_mul_weight_le hb h)

theorem integrable_fderiv_apply_mul_weight (hφ : ContDiff ℝ 1 φ)
    (ha : ((i + j : ℕ) : ℝ) + 2 < a) {w : ℂ → ℂ} (hwc : Continuous w)
    (hw : ∀ z, ‖fderiv ℝ φ z (w z)‖ ≤ C * (1 + ‖z‖) ^ (-a)) :
    Integrable fun z => fderiv ℝ φ z (w z) * weight i j z :=
  integrable_of_bound_rpow
    (((hφ.continuous_fderiv one_ne_zero).clm_apply hwc).mul
      (contDiff_weight i j).continuous).aestronglyMeasurable
    (by linarith) (norm_mul_weight_le hw le_rfl)

/-- `∫ Dφ(z)(w) p(z) = -(i w ∫ φ z^(i-1) z̄^j + j w̄ ∫ φ z^i z̄^(j-1))` for a constant
direction `w`, given `∫ D(φ p)(z)(w) = 0`. -/
theorem integral_fderiv_const_mul_weight_aux (hφ : ContDiff ℝ 1 φ)
    (ha : ((i + j : ℕ) : ℝ) + 2 < a) (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-a)) (w : ℂ)
    (hw : ∀ z, ‖fderiv ℝ φ z w‖ ≤ C * (1 + ‖z‖) ^ (-a))
    (h0 : ∫ z, fderiv ℝ (fun z => φ z * weight i j z) z w = 0) :
    ∫ z, fderiv ℝ φ z w * weight i j z =
      -((i : ℂ) * w * ∫ z, φ z * weight (i - 1) j z) -
        (j : ℂ) * starRingEnd ℂ w * ∫ z, φ z * weight i (j - 1) z := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hA := integrable_mul_weight i j hφ.continuous ha hb (i' := i - 1) (j' := j) (by omega)
  have hB := integrable_mul_weight i j hφ.continuous ha hb (i' := i) (j' := j - 1) (by omega)
  have hW : Integrable fun z => fderiv ℝ φ z w * weight i j z :=
    integrable_of_bound_rpow
      ((hfc.clm_apply continuous_const).mul (contDiff_weight i j).continuous).aestronglyMeasurable
      (by linarith) (norm_mul_weight_le hw le_rfl)
  have hpt : ∀ z, φ z * weightDeriv i j z w =
      ((i : ℂ) * w) * (φ z * weight (i - 1) j z) +
        ((j : ℂ) * starRingEnd ℂ w) * (φ z * weight i (j - 1) z) := by
    intro z
    simp only [weightDeriv, weight]
    ring
  have hsplit : ∫ z, fderiv ℝ (fun z => φ z * weight i j z) z w =
      (∫ z, fderiv ℝ φ z w * weight i j z) +
        (((i : ℂ) * w) * ∫ z, φ z * weight (i - 1) j z) +
        ((j : ℂ) * starRingEnd ℂ w) * ∫ z, φ z * weight i (j - 1) z := by
    have hAB : Integrable fun z => ((i : ℂ) * w) * (φ z * weight (i - 1) j z) +
        ((j : ℂ) * starRingEnd ℂ w) * (φ z * weight i (j - 1) z) :=
      (hA.const_mul _).add (hB.const_mul _)
    simp only [fderiv_mul_weight_apply hd, hpt]
    rw [integral_add hW hAB, integral_add (hA.const_mul _) (hB.const_mul _), integral_const_mul,
      integral_const_mul]
    ring
  rw [h0] at hsplit
  linear_combination -hsplit

/-- **Translation.** For `i + j + 2 < a`, if `φ`, `Dφ(z) 1` and `Dφ(z) i` are
`O((1 + |z|)^(-a))`, then for every `c`:
`∫ Dφ(z)(c) z^i z̄^j = -(i c ∫ φ z^(i-1) z̄^j + j c̄ ∫ φ z^i z̄^(j-1))`. -/
theorem integral_fderiv_mul_weight (hφ : ContDiff ℝ 1 φ)
    (ha : ((i + j : ℕ) : ℝ) + 2 < a) (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-a))
    (h1 : ∀ z, ‖fderiv ℝ φ z 1‖ ≤ C * (1 + ‖z‖) ^ (-a))
    (hI : ∀ z, ‖fderiv ℝ φ z Complex.I‖ ≤ C * (1 + ‖z‖) ^ (-a)) (c : ℂ) :
    ∫ z, fderiv ℝ φ z c * weight i j z =
      -((i : ℂ) * c * (∫ z, φ z * weight (i - 1) j z) +
        (j : ℂ) * starRingEnd ℂ c * ∫ z, φ z * weight i (j - 1) z) := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hψ := contDiff_mul_weight hφ i j
  have hψc : Continuous (fderiv ℝ fun z => φ z * weight i j z) :=
    hψ.continuous_fderiv one_ne_zero
  have hlim : Tendsto (fun z => φ z * weight i j z) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_cobounded_of_bound_rpow (by linarith) (norm_mul_weight_le hb le_rfl)
  have hint : ∀ v : ℂ, ‖v‖ = 1 → (∀ z, ‖fderiv ℝ φ z v‖ ≤ C * (1 + ‖z‖) ^ (-a)) →
      Integrable fun z => fderiv ℝ (fun z => φ z * weight i j z) z v := by
    intro v hv hvb
    exact integrable_of_bound_rpow (hψc.clm_apply continuous_const).aestronglyMeasurable
      (by linarith)
      (norm_fderiv_mul_weight_le hd i j hb (fun _ => v) hvb
        (fun z => norm_weightDeriv_const_le i j hv z))
  have e1 := integral_fderiv_const_mul_weight_aux i j hφ ha hb 1 h1
    (ComplexSwapJacquet.integral_fderiv_one_eq_zero hψ (hint 1 (by simp) h1) hlim)
  have eI := integral_fderiv_const_mul_weight_aux i j hφ ha hb Complex.I hI
    (ComplexSwapJacquet.integral_fderiv_I_eq_zero hψ (hint Complex.I (by simp) hI) hlim)
  have hW : ∀ v : ℂ, (∀ z, ‖fderiv ℝ φ z v‖ ≤ C * (1 + ‖z‖) ^ (-a)) →
      Integrable fun z => fderiv ℝ φ z v * weight i j z := fun v hv =>
    integrable_of_bound_rpow
      ((hfc.clm_apply continuous_const).mul (contDiff_weight i j).continuous).aestronglyMeasurable
      (by linarith) (norm_mul_weight_le hv le_rfl)
  have hpt : ∀ z, fderiv ℝ φ z c * weight i j z =
      (c.re : ℂ) * (fderiv ℝ φ z 1 * weight i j z) +
        (c.im : ℂ) * (fderiv ℝ φ z Complex.I * weight i j z) := by
    intro z
    have hw : c = c.re • (1 : ℂ) + c.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    ring
  simp only [hpt]
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  have hcc : starRingEnd ℂ c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [integral_add ((hW 1 h1).const_mul _) ((hW Complex.I hI).const_mul _), integral_const_mul,
    integral_const_mul, e1, eI, hcc]
  simp only [map_one, Complex.conj_I]
  linear_combination ((i : ℂ) * ∫ z, φ z * weight (i - 1) j z) * hc

/-- **Euler.** For `i + j + 2 < a`, if `φ` and `Dφ(z) z` are `O((1 + |z|)^(-a))`, then
`∫ Dφ(z)(z) z^i z̄^j = -(2 + i + j) ∫ φ z^i z̄^j`. -/
theorem integral_fderiv_self_mul_weight (hφ : ContDiff ℝ 1 φ)
    (ha : ((i + j : ℕ) : ℝ) + 2 < a) (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-a))
    (hz : ∀ z, ‖fderiv ℝ φ z z‖ ≤ C * (1 + ‖z‖) ^ (-a)) :
    ∫ z, fderiv ℝ φ z z * weight i j z =
      -(2 + ((i + j : ℕ) : ℂ)) * ∫ z, φ z * weight i j z := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hC : 0 ≤ C := (norm_nonneg _).trans ((hb 0).trans_eq (by simp))
  have hψ := contDiff_mul_weight hφ i j
  have hbψ : ∀ z, ‖φ z * weight i j z‖ ≤
      C * (1 + ((i + j : ℕ) : ℝ)) * (1 + ‖z‖) ^ (-(a - ((i + j : ℕ) : ℝ))) := by
    intro z
    refine (norm_mul_weight_le hb le_rfl z).trans ?_
    have : C ≤ C * (1 + ((i + j : ℕ) : ℝ)) := by
      nlinarith [(Nat.cast_nonneg (i + j) : (0 : ℝ) ≤ ((i + j : ℕ) : ℝ))]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have he := integral_fderiv_apply_self_rpow hψ (by linarith) hbψ
    (norm_fderiv_mul_weight_le hd i j hb id hz (norm_weightDeriv_self_le i j))
  have hP := integrable_mul_weight i j hφ.continuous ha hb (le_refl (i + j))
  have hW : Integrable fun z => fderiv ℝ φ z z * weight i j z :=
    integrable_of_bound_rpow
      ((hfc.clm_apply continuous_id).mul (contDiff_weight i j).continuous).aestronglyMeasurable
      (by linarith) (norm_mul_weight_le hz le_rfl)
  have hpt : ∀ z, fderiv ℝ (fun z => φ z * weight i j z) z z =
      fderiv ℝ φ z z * weight i j z + ((i + j : ℕ) : ℂ) * (φ z * weight i j z) := by
    intro z
    rw [fderiv_mul_weight_apply hd, weightDeriv_self]
    ring
  simp only [hpt] at he
  rw [integral_add hW (hP.const_mul _), integral_const_mul] at he
  linear_combination he

/-- **Rotation.** For `i + j + 2 < a`, if `φ` and `Dφ(z)(i z)` are `O((1 + |z|)^(-a))`, then
`∫ Dφ(z)(i z) z^i z̄^j = -i (i - j) ∫ φ z^i z̄^j`. -/
theorem integral_fderiv_I_mul_self_mul_weight (hφ : ContDiff ℝ 1 φ)
    (ha : ((i + j : ℕ) : ℝ) + 2 < a) (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-a))
    (hz : ∀ z, ‖fderiv ℝ φ z (Complex.I * z)‖ ≤ C * (1 + ‖z‖) ^ (-a)) :
    ∫ z, fderiv ℝ φ z (Complex.I * z) * weight i j z =
      -(Complex.I * ((i : ℂ) - (j : ℂ))) * ∫ z, φ z * weight i j z := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hC : 0 ≤ C := (norm_nonneg _).trans ((hb 0).trans_eq (by simp))
  have hψ := contDiff_mul_weight hφ i j
  have hbψ : ∀ z, ‖φ z * weight i j z‖ ≤
      C * (1 + ((i + j : ℕ) : ℝ)) * (1 + ‖z‖) ^ (-(a - ((i + j : ℕ) : ℝ))) := by
    intro z
    refine (norm_mul_weight_le hb le_rfl z).trans ?_
    have : C ≤ C * (1 + ((i + j : ℕ) : ℝ)) := by
      nlinarith [(Nat.cast_nonneg (i + j) : (0 : ℝ) ≤ ((i + j : ℕ) : ℝ))]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have he := integral_fderiv_apply_I_mul_self_rpow hψ (by linarith) hbψ
    (norm_fderiv_mul_weight_le hd i j hb (fun z => Complex.I * z) hz
      (norm_weightDeriv_I_mul_self_le i j))
  have hP := integrable_mul_weight i j hφ.continuous ha hb (le_refl (i + j))
  have hW : Integrable fun z => fderiv ℝ φ z (Complex.I * z) * weight i j z :=
    integrable_of_bound_rpow
      ((hfc.clm_apply (continuous_const.mul continuous_id)).mul
        (contDiff_weight i j).continuous).aestronglyMeasurable
      (by linarith) (norm_mul_weight_le hz le_rfl)
  have hpt : ∀ z, fderiv ℝ (fun z => φ z * weight i j z) z (Complex.I * z) =
      fderiv ℝ φ z (Complex.I * z) * weight i j z +
        (Complex.I * ((i : ℂ) - (j : ℂ))) * (φ z * weight i j z) := by
    intro z
    rw [fderiv_mul_weight_apply hd, weightDeriv_I_mul_self]
    ring
  simp only [hpt] at he
  rw [integral_add hW (hP.const_mul _), integral_const_mul] at he
  linear_combination he

end Weighted

end Langlands.Archimedean.ComplexGLTwoMoment
