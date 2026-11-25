import Langlands.MathlibBase

/-!
# Landau's theorem for Laplace transforms of nonnegative functions

Widder, *The Laplace Transform* (1941), Chapter II, §5, Theorem 5b: if a Laplace–Stieltjes
transform has a monotonic (nondecreasing) determining function `α`, that is, a nonnegative
determining measure `dα`, the real point of its axis of convergence is a singular point of
the function it represents. Nonnegativity of `α` itself is not enough. Here the measure
`c • μ` (or `f • μ`) with nonnegative density plays the role of `dα`. Chapter VI, §1,
formula (4), splits a two-sided transform into two one-sided transforms.

We work on an arbitrary measure space `(X, μ)`.

* One-sided transforms `transform μ c ℓ s = ∫ c x * exp (-ℓ x * s) dμ` with `c ≥ 0`, `ℓ ≥ 0`
  almost everywhere. `differentiableOn_transform`: holomorphy on `σc < Re s` when the
  transform converges absolutely at every real `σ > σc`. `integrableAt_of_differentiableOn`
  (Landau's theorem): if the transform converges absolutely at the real point `σ₁` and
  agrees, on `σ₁ < Re s`, with a function holomorphic on `σ₀ < Re s`, then it converges
  absolutely at every real `σ > σ₀`.
* Two-sided transforms `bilateral μ f u s = ∫ f x * exp (s * u x) dμ` with `f ≥ 0` almost
  everywhere and `u` real. `differentiableOn_bilateral`: holomorphy on `σ₀ < Re s` when the
  transform converges absolutely at every real `σ > σ₀`. `integrable_of_differentiableOn`
  (Landau's theorem): if the transform converges absolutely at every real `σ > σ₁` and
  agrees, on `σ₁ < Re s`, with a function holomorphic on `σ₀ < Re s`, then it converges
  absolutely at every real `σ > σ₀`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Metric MeasureTheory

namespace Langlands.LandauMellin

variable {X : Type*} [MeasurableSpace X]

/-! ## One-sided transforms -/

/-- The integrand `c x * exp (-ℓ x * s)` of the one-sided transform. -/
def kernel (c ℓ : X → ℝ) (s : ℂ) (x : X) : ℂ :=
  (c x : ℂ) * Complex.exp (-(ℓ x : ℂ) * s)

/-- The one-sided transform `∫ c x * exp (-ℓ x * s) dμ`. -/
def transform (μ : Measure X) (c ℓ : X → ℝ) (s : ℂ) : ℂ :=
  ∫ x, kernel c ℓ s x ∂μ

/-- Absolute convergence of the one-sided transform at the real point `σ`: integrability
of `c x * exp (-ℓ x * σ)`. -/
def IntegrableAt (μ : Measure X) (c ℓ : X → ℝ) (σ : ℝ) : Prop :=
  Integrable (fun x => c x * Real.exp (-ℓ x * σ)) μ

/-- The coefficients `c x * (-ℓ x) ^ m` of the `m`-th derivative. -/
def derivCoeff (c ℓ : X → ℝ) (m : ℕ) (x : X) : ℝ := c x * (-ℓ x) ^ m

/-- The nonnegative terms `c x * (δ * ℓ x) ^ n / n! * exp (-ℓ x * a)` of the Taylor
expansion at `a`, evaluated at `a - δ`. -/
def taylorTerm (c ℓ : X → ℝ) (δ a : ℝ) (n : ℕ) (x : X) : ℝ :=
  c x * (δ * ℓ x) ^ n / (n.factorial : ℝ) * Real.exp (-ℓ x * a)

variable {μ : Measure X}

omit [MeasurableSpace X] in
theorem norm_kernel (c ℓ : X → ℝ) (s : ℂ) (x : X) :
    ‖kernel c ℓ s x‖ = |c x| * Real.exp (-ℓ x * s.re) := by
  rw [kernel, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 2
  simp [Complex.mul_re]

omit [MeasurableSpace X] in
theorem derivCoeff_zero (c ℓ : X → ℝ) : derivCoeff c ℓ 0 = c := by
  funext x
  simp [derivCoeff]

theorem isOpen_halfPlane (σ : ℝ) : IsOpen {s : ℂ | σ < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem aestronglyMeasurable_kernel {c ℓ : X → ℝ} (hcm : AEStronglyMeasurable c μ)
    (hℓm : AEStronglyMeasurable ℓ μ) (s : ℂ) : AEStronglyMeasurable (kernel c ℓ s) μ := by
  have h1 : AEStronglyMeasurable (fun x => (c x : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hcm
  have h2 : AEStronglyMeasurable (fun x => Complex.exp (-(ℓ x : ℂ) * s)) μ :=
    (show Continuous fun t : ℝ => Complex.exp (-(t : ℂ) * s) by fun_prop).comp_aestronglyMeasurable
      hℓm
  exact h1.mul h2

theorem aestronglyMeasurable_real {c ℓ : X → ℝ} (hcm : AEStronglyMeasurable c μ)
    (hℓm : AEStronglyMeasurable ℓ μ) (σ : ℝ) :
    AEStronglyMeasurable (fun x => c x * Real.exp (-ℓ x * σ)) μ :=
  hcm.mul
    ((show Continuous fun t : ℝ => Real.exp (-t * σ) by fun_prop).comp_aestronglyMeasurable hℓm)

theorem aestronglyMeasurable_derivCoeff {c ℓ : X → ℝ} (hcm : AEStronglyMeasurable c μ)
    (hℓm : AEStronglyMeasurable ℓ μ) (m : ℕ) : AEStronglyMeasurable (derivCoeff c ℓ m) μ :=
  hcm.mul ((show Continuous fun t : ℝ => (-t) ^ m by fun_prop).comp_aestronglyMeasurable hℓm)

/-- Domination of a kernel with coefficients `a` by an absolutely convergent real
transform with coefficients `b ≥ |a|`. -/
theorem integrable_kernel_of_le {a b ℓ : X → ℝ} (ham : AEStronglyMeasurable a μ)
    (hℓm : AEStronglyMeasurable ℓ μ) (hℓ : ∀ᵐ x ∂μ, 0 ≤ ℓ x) {σ : ℝ}
    (hb : Integrable (fun x => b x * Real.exp (-ℓ x * σ)) μ) (hab : ∀ᵐ x ∂μ, |a x| ≤ b x)
    {s : ℂ} (hs : σ ≤ s.re) : Integrable (kernel a ℓ s) μ := by
  refine hb.mono' (aestronglyMeasurable_kernel ham hℓm s) ?_
  filter_upwards [hℓ, hab] with x hx hax
  rw [norm_kernel]
  exact mul_le_mul hax (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hs hx]))
    (Real.exp_pos _).le ((abs_nonneg _).trans hax)

section OneSided

variable {c ℓ : X → ℝ} (hcm : AEStronglyMeasurable c μ) (hℓm : AEStronglyMeasurable ℓ μ)
  (hc : ∀ᵐ x ∂μ, 0 ≤ c x) (hℓ : ∀ᵐ x ∂μ, 0 ≤ ℓ x)

include hcm hℓm hc hℓ

theorem integrable_kernel {s : ℂ} (h : IntegrableAt μ c ℓ s.re) :
    Integrable (kernel c ℓ s) μ :=
  integrable_kernel_of_le hcm hℓm hℓ h (hc.mono fun _ hx => (abs_of_nonneg hx).le) le_rfl

theorem IntegrableAt.mono {σ σ' : ℝ} (h : IntegrableAt μ c ℓ σ) (hσ : σ ≤ σ') :
    IntegrableAt μ c ℓ σ' := by
  refine Integrable.mono' h (aestronglyMeasurable_real hcm hℓm σ') ?_
  filter_upwards [hc, hℓ] with x hcx hℓx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcx (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hσ hℓx])) hcx

/-- Multiplying the coefficients by `ℓ x ^ m` keeps absolute convergence strictly to the
right. -/
theorem IntegrableAt.mul_pow {σ σ' : ℝ} (h : IntegrableAt μ c ℓ σ) (hσ : σ < σ') (m : ℕ) :
    IntegrableAt μ (fun x => c x * ℓ x ^ m) ℓ σ' := by
  show Integrable (fun x => c x * ℓ x ^ m * Real.exp (-ℓ x * σ')) μ
  set t := σ' - σ with ht
  have htpos : 0 < t := sub_pos.mpr hσ
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hb : ∀ y : ℝ, 0 ≤ y → y ^ m * Real.exp (-(t * y)) ≤ m.factorial / t ^ m := by
    intro y hy
    have h1 := Real.pow_div_factorial_le_exp _ (mul_nonneg htpos.le hy) m
    have he := Real.exp_pos (t * y)
    rw [div_le_iff₀ hf, _root_.mul_pow] at h1
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ he (pow_pos htpos m)]
    calc y ^ m * t ^ m = t ^ m * y ^ m := mul_comm _ _
      _ ≤ Real.exp (t * y) * m.factorial := h1
      _ = m.factorial * Real.exp (t * y) := mul_comm _ _
  have hmeas : AEStronglyMeasurable (fun x => c x * ℓ x ^ m) μ :=
    hcm.mul ((continuous_pow m).comp_aestronglyMeasurable hℓm)
  refine Integrable.mono' (Integrable.const_mul h ((m.factorial : ℝ) / t ^ m))
    (aestronglyMeasurable_real hmeas hℓm σ') ?_
  filter_upwards [hc, hℓ] with x hcx hℓx
  have he : Real.exp (-ℓ x * σ') = Real.exp (-ℓ x * σ) * Real.exp (-(t * ℓ x)) := by
    rw [← Real.exp_add]
    congr 1
    rw [ht]
    ring
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg hcx (pow_nonneg hℓx m)) (Real.exp_pos _).le), he]
  calc c x * ℓ x ^ m * (Real.exp (-ℓ x * σ) * Real.exp (-(t * ℓ x)))
      = (c x * Real.exp (-ℓ x * σ)) * (ℓ x ^ m * Real.exp (-(t * ℓ x))) := by ring
    _ ≤ (c x * Real.exp (-ℓ x * σ)) * ((m.factorial : ℝ) / t ^ m) :=
      mul_le_mul_of_nonneg_left (hb _ hℓx) (mul_nonneg hcx (Real.exp_pos _).le)
    _ = (m.factorial : ℝ) / t ^ m * (c x * Real.exp (-ℓ x * σ)) := mul_comm _ _

theorem integrableAt_mul_pow_of_forall {σc : ℝ}
    (hσ : ∀ σ, σc < σ → IntegrableAt μ c ℓ σ) (m : ℕ) {σ' : ℝ} (hσ' : σc < σ') :
    IntegrableAt μ (fun x => c x * ℓ x ^ m) ℓ σ' :=
  (hσ ((σc + σ') / 2) (by linarith)).mul_pow hcm hℓm hc hℓ (by linarith) m

omit [MeasurableSpace X] hcm hℓm hc hℓ in
theorem hasDerivAt_kernel (c ℓ : X → ℝ) (x : X) (s : ℂ) :
    HasDerivAt (fun w => kernel c ℓ w x) (kernel (fun y => c y * -ℓ y) ℓ s x) s := by
  have h := (((hasDerivAt_id s).const_mul (-(ℓ x : ℂ))).cexp).const_mul (c x : ℂ)
  simp only [id, mul_one] at h
  have e : kernel (fun y => c y * -ℓ y) ℓ s x =
      (c x : ℂ) * (Complex.exp (-(ℓ x : ℂ) * s) * -(ℓ x : ℂ)) := by
    simp only [kernel]
    push_cast
    ring
  rw [e]
  exact h

omit [MeasurableSpace X] hcm hℓm hc hℓ in
theorem hasDerivAt_kernel_derivCoeff (c ℓ : X → ℝ) (m : ℕ) (x : X) (s : ℂ) :
    HasDerivAt (fun w => kernel (derivCoeff c ℓ m) ℓ w x)
      (kernel (derivCoeff c ℓ (m + 1)) ℓ s x) s := by
  have e : derivCoeff c ℓ (m + 1) = fun y => derivCoeff c ℓ m y * -ℓ y := by
    funext y
    simp only [derivCoeff, pow_succ]
    ring
  rw [e]
  exact hasDerivAt_kernel _ ℓ x s

omit [MeasurableSpace X] hcm hℓm hc hℓ in
theorem abs_derivCoeff {x : X} (hcx : 0 ≤ c x) (hℓx : 0 ≤ ℓ x) (m : ℕ) :
    |derivCoeff c ℓ m x| = c x * ℓ x ^ m := by
  rw [derivCoeff, abs_mul, abs_of_nonneg hcx, abs_pow, abs_neg, abs_of_nonneg hℓx]

/-- Differentiation under the integral sign: the derivative of the transform with
coefficients `c (-ℓ) ^ m` is the transform with coefficients `c (-ℓ) ^ (m + 1)`. -/
theorem hasDerivAt_transform {σc : ℝ} (hσ : ∀ σ, σc < σ → IntegrableAt μ c ℓ σ) (m : ℕ)
    {s : ℂ} (hs : σc < s.re) :
    HasDerivAt (transform μ (derivCoeff c ℓ m) ℓ)
      (transform μ (derivCoeff c ℓ (m + 1)) ℓ s) s := by
  set σ' := (σc + s.re) / 2 with hσ'def
  have h1 : σc < σ' := by rw [hσ'def]; linarith
  have h2 : σ' < s.re := by rw [hσ'def]; linarith
  have hb := integrableAt_mul_pow_of_forall hcm hℓm hc hℓ hσ (m + 1) h1
  have hU : {w : ℂ | σ' < w.re} ∈ 𝓝 s := (isOpen_halfPlane σ').mem_nhds h2
  have hmeas : ∀ w, AEStronglyMeasurable (kernel (derivCoeff c ℓ m) ℓ w) μ :=
    fun w => aestronglyMeasurable_kernel (aestronglyMeasurable_derivCoeff hcm hℓm m) hℓm w
  have hint : Integrable (kernel (derivCoeff c ℓ m) ℓ s) μ :=
    integrable_kernel_of_le (aestronglyMeasurable_derivCoeff hcm hℓm m) hℓm hℓ
      (integrableAt_mul_pow_of_forall hcm hℓm hc hℓ hσ m h1)
      (by filter_upwards [hc, hℓ] with y hcx hℓx; exact (abs_derivCoeff hcx hℓx m).le) h2.le
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun w => kernel (derivCoeff c ℓ m) ℓ w)
    (F' := fun w => kernel (derivCoeff c ℓ (m + 1)) ℓ w)
    (bound := fun x => c x * ℓ x ^ (m + 1) * Real.exp (-ℓ x * σ')) hU
    (Eventually.of_forall hmeas) hint
    (aestronglyMeasurable_kernel (aestronglyMeasurable_derivCoeff hcm hℓm (m + 1)) hℓm s)
    ?_ hb (Eventually.of_forall fun x w _ => hasDerivAt_kernel_derivCoeff c ℓ m x w)
  · exact key.2
  · filter_upwards [hc, hℓ] with x hcx hℓx
    intro w hw
    rw [norm_kernel, abs_derivCoeff hcx hℓx]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hcx (pow_nonneg hℓx _))
    apply Real.exp_le_exp.mpr
    have hw' : σ' < w.re := hw
    nlinarith [mul_le_mul_of_nonneg_left hw'.le hℓx]

theorem iteratedDeriv_transform {σc : ℝ} (hσ : ∀ σ, σc < σ → IntegrableAt μ c ℓ σ) (m : ℕ)
    {s : ℂ} (hs : σc < s.re) :
    iteratedDeriv m (transform μ c ℓ) s = transform μ (derivCoeff c ℓ m) ℓ s := by
  induction m generalizing s with
  | zero => rw [iteratedDeriv_zero, derivCoeff_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (transform μ c ℓ) =ᶠ[𝓝 s] transform μ (derivCoeff c ℓ m) ℓ := by
      filter_upwards [(isOpen_halfPlane σc).mem_nhds hs] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    exact (hasDerivAt_transform hcm hℓm hc hℓ hσ m hs).deriv

/-- The transform is holomorphic on `σc < Re s` when it converges absolutely at every real
point `σ > σc`. -/
theorem differentiableOn_transform {σc : ℝ} (hσ : ∀ σ, σc < σ → IntegrableAt μ c ℓ σ) :
    DifferentiableOn ℂ (transform μ c ℓ) {s : ℂ | σc < s.re} := by
  intro s hs
  have h := hasDerivAt_transform hcm hℓm hc hℓ hσ 0 hs
  rw [derivCoeff_zero] at h
  exact h.differentiableAt.differentiableWithinAt

omit [MeasurableSpace X] hcm hℓm hc hℓ in
theorem taylorTerm_nonneg {x : X} (hcx : 0 ≤ c x) (hℓx : 0 ≤ ℓ x) {δ : ℝ} (hδ : 0 ≤ δ)
    (a : ℝ) (n : ℕ) : 0 ≤ taylorTerm c ℓ δ a n x :=
  mul_nonneg (div_nonneg (mul_nonneg hcx (pow_nonneg (mul_nonneg hδ hℓx) _))
    (Nat.cast_nonneg _)) (Real.exp_pos _).le

theorem integrable_taylorTerm {σc a : ℝ} (hσ : ∀ σ, σc < σ → IntegrableAt μ c ℓ σ)
    (ha : σc < a) (δ : ℝ) (n : ℕ) : Integrable (taylorTerm c ℓ δ a n) μ := by
  have h := Integrable.const_mul (integrableAt_mul_pow_of_forall hcm hℓm hc hℓ hσ n ha)
    (δ ^ n / (n.factorial : ℝ))
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [taylorTerm]
  rw [mul_pow]
  ring

/-- The `n`-th Taylor term of the transform at the real point `a`, evaluated at `a - δ`. -/
theorem taylor_coeff_eq {σc a : ℝ} (hσ : ∀ σ, σc < σ → IntegrableAt μ c ℓ σ) (ha : σc < a)
    (δ : ℝ) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ • (((a - δ : ℝ) : ℂ) - (a : ℂ)) ^ n •
        iteratedDeriv n (transform μ c ℓ) (a : ℂ) =
      ((∫ x, taylorTerm c ℓ δ a n x ∂μ : ℝ) : ℂ) := by
  have ha' : σc < (a : ℂ).re := by rw [Complex.ofReal_re]; exact ha
  rw [iteratedDeriv_transform hcm hℓm hc hℓ hσ n ha', ← integral_complex_ofReal]
  have h1 : ((a - δ : ℝ) : ℂ) - (a : ℂ) = -(δ : ℂ) := by push_cast; ring
  rw [h1, transform, smul_eq_mul, smul_eq_mul, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext x
  simp only [kernel, derivCoeff, taylorTerm]
  push_cast
  have h2 : (-(δ : ℂ)) ^ n * (-(ℓ x : ℂ)) ^ n = ((δ : ℂ) * (ℓ x : ℂ)) ^ n := by
    rw [← mul_pow, neg_mul_neg]
  rw [← h2]
  ring

/-- **The Taylor step.** If `g` is holomorphic on the disc of radius `R` around the real
point `a`, to the right of the abscissa `σc`, and agrees with the transform there, then the
transform converges absolutely at `a - δ` for every `0 ≤ δ < R`. -/
theorem integrableAt_sub_of_taylor {σc a R δ : ℝ} (hσ : ∀ σ, σc < σ → IntegrableAt μ c ℓ σ)
    (ha : σc < a) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball (a : ℂ) R))
    (hgD : ∀ s : ℂ, σc < s.re → s ∈ Metric.ball (a : ℂ) R → g s = transform μ c ℓ s)
    (hδ0 : 0 ≤ δ) (hδ : δ < R) : IntegrableAt μ c ℓ (a - δ) := by
  have hR : 0 < R := lt_of_le_of_lt hδ0 hδ
  have hz : ((a - δ : ℝ) : ℂ) ∈ Metric.ball (a : ℂ) R := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show a - δ - a = -δ by ring, abs_neg, abs_of_nonneg hδ0]
    exact hδ
  have hT := Complex.hasSum_taylorSeries_on_ball hg hz
  have hev : g =ᶠ[𝓝 (a : ℂ)] transform μ c ℓ := by
    have hmem : (a : ℂ) ∈ {s : ℂ | σc < s.re} ∩ Metric.ball (a : ℂ) R :=
      ⟨show σc < (a : ℂ).re by rw [Complex.ofReal_re]; exact ha, Metric.mem_ball_self hR⟩
    filter_upwards [((isOpen_halfPlane σc).inter Metric.isOpen_ball).mem_nhds hmem] with s hs
    exact hgD s hs.1 hs.2
  have hsum : HasSum (fun n : ℕ => ((∫ x, taylorTerm c ℓ δ a n x ∂μ : ℝ) : ℂ))
      (g ((a - δ : ℝ) : ℂ)) := by
    convert hT using 1
    funext n
    rw [hev.iteratedDeriv_eq n]
    exact (taylor_coeff_eq hcm hℓm hc hℓ hσ ha δ n).symm
  have hsr : Summable fun n : ℕ => ∫ x, taylorTerm c ℓ δ a n x ∂μ :=
    Complex.summable_ofReal.mp hsum.summable
  have hint : ∀ n, Integrable (taylorTerm c ℓ δ a n) μ :=
    integrable_taylorTerm hcm hℓm hc hℓ hσ ha δ
  -- the pointwise expansion of `exp (δ ℓ)`
  have hpt : ∀ x, HasSum (fun n : ℕ => taylorTerm c ℓ δ a n x)
      (c x * Real.exp (-ℓ x * (a - δ))) := by
    intro x
    have hexp : HasSum (fun n : ℕ => (δ * ℓ x) ^ n / (n.factorial : ℝ))
        (Real.exp (δ * ℓ x)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (δ * ℓ x)
    have h3 := (hexp.mul_left (c x)).mul_right (Real.exp (-ℓ x * a))
    convert h3 using 1
    · funext n
      simp only [taylorTerm]
      ring
    · rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
  show Integrable (fun x => c x * Real.exp (-ℓ x * (a - δ))) μ
  refine ⟨aestronglyMeasurable_real hcm hℓm (a - δ), ?_⟩
  have hnn : 0 ≤ᵐ[μ] fun x => c x * Real.exp (-ℓ x * (a - δ)) :=
    hc.mono fun x hx => mul_nonneg hx (Real.exp_pos _).le
  rw [hasFiniteIntegral_iff_ofReal hnn]
  have hlin : ∫⁻ x, ENNReal.ofReal (c x * Real.exp (-ℓ x * (a - δ))) ∂μ =
      ∑' n, ∫⁻ x, ENNReal.ofReal (taylorTerm c ℓ δ a n x) ∂μ := by
    rw [← lintegral_tsum fun n => (hint n).aemeasurable.ennreal_ofReal]
    apply lintegral_congr_ae
    filter_upwards [hc, hℓ] with x hcx hℓx
    rw [← (hpt x).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun n => taylorTerm_nonneg hcx hℓx hδ0 a n) (hpt x).summable]
  have hterm : ∀ n, ∫⁻ x, ENNReal.ofReal (taylorTerm c ℓ δ a n x) ∂μ =
      ENNReal.ofReal (∫ x, taylorTerm c ℓ δ a n x ∂μ) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hint n)]
    filter_upwards [hc, hℓ] with x hcx hℓx
    exact taylorTerm_nonneg hcx hℓx hδ0 a n
  have hnn' : ∀ n, 0 ≤ ∫ x, taylorTerm c ℓ δ a n x ∂μ := by
    intro n
    apply integral_nonneg_of_ae
    filter_upwards [hc, hℓ] with x hcx hℓx
    exact taylorTerm_nonneg hcx hℓx hδ0 a n
  rw [hlin, tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg hnn' hsr]
  exact ENNReal.ofReal_lt_top

/-- **Landau's theorem at the abscissa.** If the transform converges absolutely to the right
of `σc` and agrees there with a function holomorphic on a disc around `σc`, it converges
absolutely at some real point to the left of `σc`. -/
theorem exists_integrableAt_lt {σc ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ σ, σc < σ → IntegrableAt μ c ℓ σ) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (σc : ℂ) ε))
    (hgD : ∀ s : ℂ, σc < s.re → g s = transform μ c ℓ s) :
    ∃ σ, σ < σc ∧ IntegrableAt μ c ℓ σ := by
  refine ⟨σc + ε / 4 - 3 * ε / 8, by linarith, ?_⟩
  refine integrableAt_sub_of_taylor hcm hℓm hc hℓ hσ (a := σc + ε / 4) (R := ε / 2)
    (by linarith) (hg.mono ?_) (fun s hs _ => hgD s hs) (by linarith) (by linarith)
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  have hd : dist ((σc + ε / 4 : ℝ) : ℂ) (σc : ℂ) = ε / 4 := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show σc + ε / 4 - σc = ε / 4 by ring, abs_of_pos (by linarith)]
  calc dist z (σc : ℂ) ≤ dist z ((σc + ε / 4 : ℝ) : ℂ) + dist ((σc + ε / 4 : ℝ) : ℂ) (σc : ℂ) :=
        dist_triangle _ _ _
    _ < ε := by rw [hd]; linarith

/-- The infimum argument: if no abscissa `σc > σ₀` of the transform is final, then the
transform converges absolutely at every real point to the right of `σ₀`. -/
theorem integrableAt_of_abscissa {σ₀ σ₁ : ℝ} (h₁ : IntegrableAt μ c ℓ σ₁)
    (hstep : ∀ σc : ℝ, σ₀ < σc → (∀ σ, σc < σ → IntegrableAt μ c ℓ σ) →
      ∃ σ, σ < σc ∧ IntegrableAt μ c ℓ σ) :
    ∀ σ, σ₀ < σ → IntegrableAt μ c ℓ σ := by
  intro σ₂ h₂
  by_contra hn
  have hlow : ∀ σ ∈ {σ : ℝ | IntegrableAt μ c ℓ σ}, σ₂ ≤ σ := by
    intro σ hσ
    by_contra hlt
    exact hn (IntegrableAt.mono hcm hℓm hc hℓ hσ (le_of_lt (not_le.mp hlt)))
  have hne : ({σ : ℝ | IntegrableAt μ c ℓ σ}).Nonempty := ⟨σ₁, h₁⟩
  have hbdd : BddBelow {σ : ℝ | IntegrableAt μ c ℓ σ} := ⟨σ₂, hlow⟩
  have hσc : σ₂ ≤ sInf {σ : ℝ | IntegrableAt μ c ℓ σ} := le_csInf hne hlow
  have habove : ∀ σ, sInf {σ : ℝ | IntegrableAt μ c ℓ σ} < σ → IntegrableAt μ c ℓ σ := by
    intro σ hσ
    obtain ⟨σ', hσ'A, hσ'lt⟩ := exists_lt_of_csInf_lt hne hσ
    exact IntegrableAt.mono hcm hℓm hc hℓ hσ'A hσ'lt.le
  obtain ⟨σ, hσlt, hσA⟩ := hstep _ (lt_of_lt_of_le h₂ hσc) habove
  exact absurd (csInf_le hbdd hσA) (not_le.mpr hσlt)

end OneSided

/-- Identity theorem on a right half-plane. -/
theorem eqOn_halfPlane {f g : ℂ → ℂ} {σc σ₁ : ℝ}
    (hf : DifferentiableOn ℂ f {s : ℂ | σc < s.re})
    (hg : DifferentiableOn ℂ g {s : ℂ | σc < s.re})
    (h : ∀ s : ℂ, σ₁ < s.re → f s = g s) : Set.EqOn f g {s : ℂ | σc < s.re} := by
  have hz₀ : ((max σ₁ σc + 1 : ℝ) : ℂ) ∈ {s : ℂ | σc < s.re} := by
    show σc < ((max σ₁ σc + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith [le_max_right σ₁ σc]
  refine (hf.analyticOnNhd (isOpen_halfPlane σc)).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd (isOpen_halfPlane σc)) (convex_halfSpace_re_gt σc).isPreconnected hz₀ ?_
  have hz₁ : ((max σ₁ σc + 1 : ℝ) : ℂ) ∈ {s : ℂ | σ₁ < s.re} := by
    show σ₁ < ((max σ₁ σc + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith [le_max_left σ₁ σc]
  filter_upwards [(isOpen_halfPlane σ₁).mem_nhds hz₁] with s hs
  exact h s hs

theorem ball_subset_halfPlane {σ₀ σc : ℝ} :
    Metric.ball (σc : ℂ) (σc - σ₀) ⊆ {s : ℂ | σ₀ < s.re} := by
  intro z hz
  rw [Metric.mem_ball, Complex.dist_eq] at hz
  have h := Complex.abs_re_le_norm (z - σc)
  rw [Complex.sub_re, Complex.ofReal_re] at h
  show σ₀ < z.re
  linarith [neg_abs_le (z.re - σc)]

/-- **Landau's theorem for one-sided transforms** (Widder 1941, Chapter II, Theorem 5b). Let
`c ≥ 0` and `ℓ ≥ 0` almost everywhere. If `∫ c x * exp (-ℓ x * s) dμ` converges absolutely at
the real point `σ₁` and agrees, on `σ₁ < Re s`, with a function holomorphic on
`σ₀ < Re s`, then it converges absolutely at every real `σ > σ₀`. -/
theorem integrableAt_of_differentiableOn {c ℓ : X → ℝ} (hcm : AEStronglyMeasurable c μ)
    (hℓm : AEStronglyMeasurable ℓ μ) (hc : ∀ᵐ x ∂μ, 0 ≤ c x) (hℓ : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    {σ₀ σ₁ : ℝ} (h₁ : IntegrableAt μ c ℓ σ₁) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {s : ℂ | σ₀ < s.re})
    (hgD : ∀ s : ℂ, σ₁ < s.re → g s = transform μ c ℓ s) :
    ∀ σ, σ₀ < σ → IntegrableAt μ c ℓ σ := by
  refine integrableAt_of_abscissa hcm hℓm hc hℓ h₁ (fun σc hσc habove => ?_)
  have hsub : {s : ℂ | σc < s.re} ⊆ {s : ℂ | σ₀ < s.re} := fun s (hs : σc < s.re) =>
    show σ₀ < s.re from lt_trans hσc hs
  have heq := eqOn_halfPlane (hg.mono hsub)
    (differentiableOn_transform hcm hℓm hc hℓ habove) hgD
  exact exists_integrableAt_lt hcm hℓm hc hℓ (sub_pos.mpr hσc) habove
    (hg.mono ball_subset_halfPlane) (fun s hs => heq hs)

/-! ## Two-sided transforms -/

/-- The two-sided transform `∫ f x * exp (s * u x) dμ`. -/
def bilateral (μ : Measure X) (f u : X → ℝ) (s : ℂ) : ℂ :=
  ∫ x, (f x : ℂ) * Complex.exp (s * (u x : ℂ)) ∂μ

section TwoSided

variable {f u : X → ℝ} (hfm : AEStronglyMeasurable f μ) (hum : AEStronglyMeasurable u μ)
  (hf : ∀ᵐ x ∂μ, 0 ≤ f x)

omit [MeasurableSpace X] in
theorem kernel_neg_eq (f u : X → ℝ) (s : ℂ) (x : X) :
    kernel f (fun y => -u y) s x = (f x : ℂ) * Complex.exp (s * (u x : ℂ)) := by
  rw [kernel, Complex.ofReal_neg, neg_neg, mul_comm (u x : ℂ)]

omit [MeasurableSpace X] in
theorem kernel_eq_neg (f u : X → ℝ) (s : ℂ) (x : X) :
    kernel f u (-s) x = (f x : ℂ) * Complex.exp (s * (u x : ℂ)) := by
  rw [kernel]
  congr 2
  ring

omit [MeasurableSpace X] in
theorem real_neg_eq (f u : X → ℝ) (σ : ℝ) :
    (fun x => f x * Real.exp (-(-u x) * σ)) = fun x => f x * Real.exp (σ * u x) := by
  funext x
  rw [neg_neg, mul_comm (u x)]

omit [MeasurableSpace X] in
theorem real_eq_neg (f u : X → ℝ) (σ : ℝ) :
    (fun x => f x * Real.exp (-u x * σ)) = fun x => f x * Real.exp (-σ * u x) := by
  funext x
  congr 2
  ring

include hfm hum hf

/-- Absolute convergence of the two-sided transform at a complex point. -/
theorem integrable_bilateral {s : ℂ}
    (h : Integrable (fun x => f x * Real.exp (s.re * u x)) μ) :
    Integrable (fun x => (f x : ℂ) * Complex.exp (s * (u x : ℂ))) μ := by
  refine h.mono' ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hfm).mul
      ((show Continuous fun t : ℝ => Complex.exp (s * (t : ℂ)) by fun_prop).comp_aestronglyMeasurable
        hum)
  · filter_upwards [hf] with x hx
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]

omit hfm hf in
theorem nullMeasurableSet_neg : NullMeasurableSet {x | u x < 0} μ :=
  hum.nullMeasurableSet_lt aestronglyMeasurable_const

omit hfm hf in
/-- The two-sided transform splits into a one-sided transform over `{u < 0}` and a one-sided
transform at `-s` over `{u ≥ 0}`. -/
theorem bilateral_eq_add {s : ℂ}
    (hi : Integrable (fun x => (f x : ℂ) * Complex.exp (s * (u x : ℂ))) μ) :
    bilateral μ f u s = transform (μ.restrict {x | u x < 0}) f (fun x => -u x) s +
      transform (μ.restrict {x | u x < 0}ᶜ) f u (-s) := by
  simp only [transform, kernel_neg_eq, kernel_eq_neg]
  rw [bilateral, integral_add_compl₀ (nullMeasurableSet_neg hum) hi]

/-- On `{u ≥ 0}`, absolute convergence at every real point `σ > σ₁` propagates to every
real point. -/
theorem integrableOn_compl {σ₁ : ℝ}
    (h₁ : ∀ σ : ℝ, σ₁ < σ → Integrable (fun x => f x * Real.exp (σ * u x)) μ) (σ : ℝ) :
    IntegrableOn (fun x => f x * Real.exp (σ * u x)) {x | u x < 0}ᶜ μ := by
  have hlt : σ₁ < max σ₁ σ + 1 := by linarith [le_max_left σ₁ σ]
  refine Integrable.mono' (h₁ (max σ₁ σ + 1) hlt).restrict ?_ ?_
  · exact (hfm.mul ((show Continuous fun t : ℝ => Real.exp (σ * t) by
      fun_prop).comp_aestronglyMeasurable hum)).restrict
  · filter_upwards [ae_restrict_mem₀ (nullMeasurableSet_neg hum).compl,
      ae_restrict_of_ae hf] with x hx hfx
    have hux : 0 ≤ u x := not_lt.mp hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfx (Real.exp_pos _).le)]
    have hσle : σ ≤ max σ₁ σ + 1 := by linarith [le_max_right σ₁ σ]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hσle hux])) hfx

/-- The one-sided transform over `{u ≥ 0}`, evaluated at `-s`, is entire when the two-sided
transform converges absolutely at every real point `σ > σ₁`. -/
theorem differentiable_compl {σ₁ : ℝ}
    (h₁ : ∀ σ : ℝ, σ₁ < σ → Integrable (fun x => f x * Real.exp (σ * u x)) μ) :
    Differentiable ℂ (fun s => transform (μ.restrict {x | u x < 0}ᶜ) f u (-s)) := by
  have hB : ∀ τ : ℝ, IntegrableAt (μ.restrict {x | u x < 0}ᶜ) f u τ := by
    intro τ
    show Integrable (fun x => f x * Real.exp (-u x * τ)) (μ.restrict {x | u x < 0}ᶜ)
    rw [real_eq_neg]
    exact integrableOn_compl hfm hum hf h₁ (-τ)
  have hℓB : ∀ᵐ x ∂(μ.restrict {x | u x < 0}ᶜ), 0 ≤ u x :=
    (ae_restrict_mem₀ (nullMeasurableSet_neg hum).compl).mono fun x hx => not_lt.mp hx
  intro s
  have hD := differentiableOn_transform hfm.restrict hum.restrict (ae_restrict_of_ae hf) hℓB
    (σc := -s.re - 1) (fun τ _ => hB τ)
  have hs : (-s) ∈ {w : ℂ | -s.re - 1 < w.re} := by
    show -s.re - 1 < (-s).re
    rw [Complex.neg_re]
    linarith
  have hat := hD.differentiableAt ((isOpen_halfPlane _).mem_nhds hs)
  exact hat.comp s (differentiable_neg s)

/-- The two-sided transform is holomorphic on `σ₀ < Re s` when it converges absolutely at
every real point `σ > σ₀`. -/
theorem differentiableOn_bilateral {σ₀ : ℝ}
    (h : ∀ σ : ℝ, σ₀ < σ → Integrable (fun x => f x * Real.exp (σ * u x)) μ) :
    DifferentiableOn ℂ (bilateral μ f u) {s : ℂ | σ₀ < s.re} := by
  have hA := nullMeasurableSet_neg (μ := μ) hum
  have hℓA : ∀ᵐ x ∂(μ.restrict {x | u x < 0}), 0 ≤ -u x :=
    (ae_restrict_mem₀ hA).mono fun x hx => by
      have hx' : u x < 0 := hx
      linarith
  have hIA : ∀ σ, σ₀ < σ → IntegrableAt (μ.restrict {x | u x < 0}) f (fun x => -u x) σ := by
    intro σ hσ
    show Integrable (fun x => f x * Real.exp (-(-u x) * σ)) _
    rw [real_neg_eq]
    exact (h σ hσ).restrict
  have hDA := differentiableOn_transform (ℓ := fun x => -u x) hfm.restrict hum.neg.restrict
    (ae_restrict_of_ae hf) hℓA hIA
  have hDB := differentiable_compl hfm hum hf h
  refine (hDA.add hDB.differentiableOn).congr fun s hs => ?_
  exact bilateral_eq_add hum (integrable_bilateral hfm hum hf (h s.re hs))

/-- **Landau's theorem for two-sided transforms** (Widder 1941, Chapter II, Theorem 5b, with
the bilateral splitting of Chapter VI, §1, formula (4)). Let `f ≥ 0` almost everywhere. If
`∫ f x * exp (s * u x) dμ` converges absolutely at every real point `σ > σ₁` and agrees, on
`σ₁ < Re s`, with a function holomorphic on `σ₀ < Re s`, then it converges absolutely at
every real point `σ > σ₀`. -/
theorem integrable_of_differentiableOn {σ₀ σ₁ : ℝ}
    (h₁ : ∀ σ : ℝ, σ₁ < σ → Integrable (fun x => f x * Real.exp (σ * u x)) μ) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {s : ℂ | σ₀ < s.re})
    (hgD : ∀ s : ℂ, σ₁ < s.re → g s = bilateral μ f u s) :
    ∀ σ : ℝ, σ₀ < σ → Integrable (fun x => f x * Real.exp (σ * u x)) μ := by
  intro σ hσ
  have hA := nullMeasurableSet_neg (μ := μ) hum
  have hℓA : ∀ᵐ x ∂(μ.restrict {x | u x < 0}), 0 ≤ -u x :=
    (ae_restrict_mem₀ hA).mono fun x hx => by
      have hx' : u x < 0 := hx
      linarith
  have hIA : IntegrableAt (μ.restrict {x | u x < 0}) f (fun x => -u x) (σ₁ + 1) := by
    show Integrable (fun x => f x * Real.exp (-(-u x) * (σ₁ + 1))) _
    rw [real_neg_eq]
    exact (h₁ (σ₁ + 1) (by linarith)).restrict
  have hDB := differentiable_compl hfm hum hf h₁
  have hL := integrableAt_of_differentiableOn (ℓ := fun x => -u x) hfm.restrict hum.neg.restrict
    (ae_restrict_of_ae hf) hℓA hIA
    (g := fun s => g s - transform (μ.restrict {x | u x < 0}ᶜ) f u (-s))
    (hg.sub hDB.differentiableOn) (fun s hs => by
      rw [hgD s (by linarith), bilateral_eq_add hum
        (integrable_bilateral hfm hum hf (h₁ s.re (by linarith)))]
      ring) σ hσ
  have hIA' : IntegrableOn (fun x => f x * Real.exp (σ * u x)) {x | u x < 0} μ := by
    have h' : Integrable (fun x => f x * Real.exp (-(-u x) * σ)) (μ.restrict {x | u x < 0}) :=
      hL
    rwa [real_neg_eq] at h'
  rw [← integrableOn_univ, ← Set.union_compl_self {x | u x < 0}]
  exact hIA'.union (integrableOn_compl hfm hum hf h₁ σ)

end TwoSided

end Langlands.LandauMellin
