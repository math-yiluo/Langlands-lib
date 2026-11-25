import Langlands.MathlibBase

/-!
# Landau's theorem for general Dirichlet series with nonnegative coefficients

Hardy and Riesz (1915), *The general theory of Dirichlet's series*, Theorem 10, p.10: if all
coefficients of a Dirichlet series `∑ cᵢ exp (-ℓᵢ s)` are nonnegative, the real point of its
line of convergence is a singular point of the function it represents.

The series here are indexed by an arbitrary type `ι`, with real coefficients `c i ≥ 0` and
real exponents `ℓ i ≥ 0`.

* `GeneralDirichlet.summableAt_of_differentiableOn` (Landau's theorem): if the series converges
  at some real point and agrees, to the right of it, with a function holomorphic on the
  half-plane `σ₀ < Re s`, then it converges at every real `σ > σ₀`.
* `GeneralDirichlet.summableAt_of_exp`: the same conclusion when only the exponential of the
  series continues holomorphically, provided the exponents are bounded below by some
  `ℓ₀ > 0`. The proof applies the local form of Landau's theorem to `-L'/L`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Metric

namespace Langlands.GeneralDirichlet

variable {ι : Type*}

/-- The term `c i * exp (-ℓ i * s)` of a general Dirichlet series. -/
def term (c ℓ : ι → ℝ) (i : ι) (s : ℂ) : ℂ := (c i : ℂ) * Complex.exp (-(ℓ i : ℂ) * s)

/-- The general Dirichlet series `∑' i, c i * exp (-ℓ i * s)`. -/
def series (c ℓ : ι → ℝ) (s : ℂ) : ℂ := ∑' i, term c ℓ i s

/-- Convergence of the series at the real point `σ`: summability of
`c i * exp (-ℓ i * σ)`. -/
def SummableAt (c ℓ : ι → ℝ) (σ : ℝ) : Prop :=
  Summable fun i => c i * Real.exp (-ℓ i * σ)

/-- The coefficients `c i * (-ℓ i) ^ m` of the `m`-th derivative. -/
def derivCoeff (c ℓ : ι → ℝ) (m : ℕ) (i : ι) : ℝ := c i * (-ℓ i) ^ m

/-- The nonnegative terms `c i * (δ * ℓ i) ^ n / n! * exp (-ℓ i * a)` of the Taylor
expansion at `a`, evaluated at `a - δ`. -/
def taylorTerm (c ℓ : ι → ℝ) (δ a : ℝ) (p : ℕ × ι) : ℝ :=
  c p.2 * (δ * ℓ p.2) ^ p.1 / (p.1.factorial : ℝ) * Real.exp (-ℓ p.2 * a)

theorem norm_term (c ℓ : ι → ℝ) (i : ι) (s : ℂ) :
    ‖term c ℓ i s‖ = |c i| * Real.exp (-ℓ i * s.re) := by
  rw [term, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 2
  simp [Complex.mul_re]

theorem term_ofReal (c ℓ : ι → ℝ) (i : ι) (σ : ℝ) :
    term c ℓ i (σ : ℂ) = ((c i * Real.exp (-ℓ i * σ) : ℝ) : ℂ) := by
  rw [term]
  push_cast
  rfl

theorem series_ofReal (c ℓ : ι → ℝ) (σ : ℝ) :
    series c ℓ (σ : ℂ) = ((∑' i, c i * Real.exp (-ℓ i * σ) : ℝ) : ℂ) := by
  rw [series, Complex.ofReal_tsum]
  exact tsum_congr fun i => term_ofReal c ℓ i σ

theorem derivCoeff_zero (c ℓ : ι → ℝ) : derivCoeff c ℓ 0 = c := by
  funext i
  simp [derivCoeff]

variable {c ℓ : ι → ℝ}

theorem SummableAt.mono (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σ σ' : ℝ}
    (h : SummableAt c ℓ σ) (hσ : σ ≤ σ') : SummableAt c ℓ σ' := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hc i) (Real.exp_pos _).le)
    (fun i => ?_) h
  apply mul_le_mul_of_nonneg_left _ (hc i)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (hℓ i) (sub_nonneg.mpr hσ)]

/-- Multiplying the coefficients by `ℓ i ^ m` keeps convergence strictly to the right. -/
theorem SummableAt.mul_pow (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σ σ' : ℝ}
    (h : SummableAt c ℓ σ) (hσ : σ < σ') (m : ℕ) :
    SummableAt (fun i => c i * ℓ i ^ m) ℓ σ' := by
  set t := σ' - σ with ht
  have htpos : 0 < t := sub_pos.mpr hσ
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hb : ∀ i, ℓ i ^ m * Real.exp (-(t * ℓ i)) ≤ m.factorial / t ^ m := by
    intro i
    have h1 := Real.pow_div_factorial_le_exp _ (mul_nonneg htpos.le (hℓ i)) m
    have he := Real.exp_pos (t * ℓ i)
    rw [div_le_iff₀ hf, _root_.mul_pow] at h1
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ he (pow_pos htpos m)]
    calc ℓ i ^ m * t ^ m = t ^ m * ℓ i ^ m := mul_comm _ _
      _ ≤ Real.exp (t * ℓ i) * m.factorial := h1
      _ = m.factorial * Real.exp (t * ℓ i) := mul_comm _ _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    (h.mul_right ((m.factorial : ℝ) / t ^ m))
  · exact mul_nonneg (mul_nonneg (hc i) (pow_nonneg (hℓ i) m)) (Real.exp_pos _).le
  · have he : Real.exp (-ℓ i * σ') = Real.exp (-ℓ i * σ) * Real.exp (-(t * ℓ i)) := by
      rw [← Real.exp_add]
      congr 1
      rw [ht]
      ring
    show c i * ℓ i ^ m * Real.exp (-ℓ i * σ') ≤
      c i * Real.exp (-ℓ i * σ) * ((m.factorial : ℝ) / t ^ m)
    rw [he]
    calc c i * ℓ i ^ m * (Real.exp (-ℓ i * σ) * Real.exp (-(t * ℓ i)))
        = (c i * Real.exp (-ℓ i * σ)) * (ℓ i ^ m * Real.exp (-(t * ℓ i))) := by ring
      _ ≤ (c i * Real.exp (-ℓ i * σ)) * ((m.factorial : ℝ) / t ^ m) :=
        mul_le_mul_of_nonneg_left (hb i) (mul_nonneg (hc i) (Real.exp_pos _).le)

theorem summableAt_mul_pow_of_forall (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σc : ℝ}
    (hσ : ∀ σ, σc < σ → SummableAt c ℓ σ) (m : ℕ) {σ' : ℝ} (hσ' : σc < σ') :
    SummableAt (fun i => c i * ℓ i ^ m) ℓ σ' :=
  (hσ ((σc + σ') / 2) (by linarith)).mul_pow hℓ hc (by linarith) m

theorem hasDerivAt_term (c ℓ : ι → ℝ) (i : ι) (s : ℂ) :
    HasDerivAt (term c ℓ i) (term (fun j => c j * -ℓ j) ℓ i s) s := by
  have h := (((hasDerivAt_id s).const_mul (-(ℓ i : ℂ))).cexp).const_mul (c i : ℂ)
  simp only [id, mul_one] at h
  have e : term (fun j => c j * -ℓ j) ℓ i s =
      (c i : ℂ) * (Complex.exp (-(ℓ i : ℂ) * s) * -(ℓ i : ℂ)) := by
    simp only [term]
    push_cast
    ring
  rw [e]
  exact h

theorem isOpen_halfPlane (σ : ℝ) : IsOpen {s : ℂ | σ < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem abs_derivCoeff (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) (m : ℕ) (i : ι) :
    |derivCoeff c ℓ m i| = c i * ℓ i ^ m := by
  rw [derivCoeff, abs_mul, abs_of_nonneg (hc i), abs_pow, abs_neg, abs_of_nonneg (hℓ i)]

/-- Termwise differentiation of the series of the `m`-th derivative coefficients. -/
theorem hasSum_deriv_series (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σc : ℝ}
    (hσ : ∀ σ, σc < σ → SummableAt c ℓ σ) (m : ℕ) {s : ℂ} (hs : σc < s.re) :
    HasSum (fun i => term (derivCoeff c ℓ (m + 1)) ℓ i s)
      (deriv (series (derivCoeff c ℓ m) ℓ) s) := by
  set σ' := (σc + s.re) / 2 with hσ'def
  have h1 : σc < σ' := by rw [hσ'def]; linarith
  have h2 : σ' < s.re := by rw [hσ'def]; linarith
  have hu := summableAt_mul_pow_of_forall hℓ hc hσ m h1
  have hd := hasSum_deriv_of_summable_norm (F := fun i => term (derivCoeff c ℓ m) ℓ i)
    (U := {w : ℂ | σ' < w.re}) hu
    (fun i w _ => (hasDerivAt_term _ ℓ i w).differentiableAt.differentiableWithinAt)
    (isOpen_halfPlane σ') (fun i w hw => ?_) (show σ' < s.re from h2)
  · have e : (fun i => term (derivCoeff c ℓ (m + 1)) ℓ i s) =
        fun i => deriv (term (derivCoeff c ℓ m) ℓ i) s := by
      funext i
      rw [(hasDerivAt_term _ ℓ i s).deriv]
      simp only [term, derivCoeff, pow_succ]
      push_cast
      ring
    rw [e]
    exact hd
  · rw [norm_term, abs_derivCoeff hℓ hc]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hc i) (pow_nonneg (hℓ i) m))
    apply Real.exp_le_exp.mpr
    have hw' : σ' < w.re := hw
    nlinarith [mul_le_mul_of_nonneg_left hw'.le (hℓ i)]

theorem iteratedDeriv_series (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σc : ℝ}
    (hσ : ∀ σ, σc < σ → SummableAt c ℓ σ) (m : ℕ) {s : ℂ} (hs : σc < s.re) :
    iteratedDeriv m (series c ℓ) s = series (derivCoeff c ℓ m) ℓ s := by
  induction m generalizing s with
  | zero => rw [iteratedDeriv_zero, derivCoeff_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (series c ℓ) =ᶠ[𝓝 s] series (derivCoeff c ℓ m) ℓ := by
      filter_upwards [(isOpen_halfPlane σc).mem_nhds hs] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    exact (hasSum_deriv_series hℓ hc hσ m hs).tsum_eq.symm

theorem differentiableOn_series (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σc : ℝ}
    (hσ : ∀ σ, σc < σ → SummableAt c ℓ σ) :
    DifferentiableOn ℂ (series c ℓ) {s : ℂ | σc < s.re} := by
  intro s hs
  have hs' : σc < s.re := hs
  set σ' := (σc + s.re) / 2 with hσ'def
  have h1 : σc < σ' := by rw [hσ'def]; linarith
  have h2 : σ' < s.re := by rw [hσ'def]; linarith
  have hD : DifferentiableOn ℂ (fun w => ∑' i, term c ℓ i w) {w : ℂ | σ' < w.re} :=
    differentiableOn_tsum_of_summable_norm (F := fun i => term c ℓ i) (hσ σ' h1)
      (fun i w _ => (hasDerivAt_term c ℓ i w).differentiableAt.differentiableWithinAt)
      (isOpen_halfPlane σ') (fun i w hw => by
        rw [norm_term, abs_of_nonneg (hc i)]
        apply mul_le_mul_of_nonneg_left _ (hc i)
        apply Real.exp_le_exp.mpr
        have hw' : σ' < w.re := hw
        nlinarith [mul_le_mul_of_nonneg_left hw'.le (hℓ i)])
  exact (hD.differentiableAt ((isOpen_halfPlane σ').mem_nhds h2)).differentiableWithinAt

theorem hasDerivAt_series (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σc : ℝ}
    (hσ : ∀ σ, σc < σ → SummableAt c ℓ σ) {s : ℂ} (hs : σc < s.re) :
    HasDerivAt (series c ℓ) (-series (fun i => c i * ℓ i) ℓ s) s := by
  have hdiff : DifferentiableAt ℂ (series c ℓ) s :=
    (differentiableOn_series hℓ hc hσ s hs).differentiableAt
      ((isOpen_halfPlane σc).mem_nhds hs)
  have hsum := hasSum_deriv_series hℓ hc hσ 0 hs
  rw [derivCoeff_zero] at hsum
  have e : deriv (series c ℓ) s = -series (fun i => c i * ℓ i) ℓ s := by
    rw [← hsum.tsum_eq, series, ← tsum_neg]
    congr 1
    funext i
    simp only [term, derivCoeff]
    push_cast
    ring
  rw [← e]
  exact hdiff.hasDerivAt

theorem taylorTerm_nonneg (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ)
    (a : ℝ) (p : ℕ × ι) : 0 ≤ taylorTerm c ℓ δ a p :=
  mul_nonneg (div_nonneg (mul_nonneg (hc _) (pow_nonneg (mul_nonneg hδ (hℓ _)) _))
    (Nat.cast_nonneg _)) (Real.exp_pos _).le

/-- The `n`-th Taylor term of the series at the real point `a`, evaluated at `a - δ`. -/
theorem taylor_coeff_eq (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σc a : ℝ}
    (hσ : ∀ σ, σc < σ → SummableAt c ℓ σ) (ha : σc < a) (δ : ℝ) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ • (((a - δ : ℝ) : ℂ) - (a : ℂ)) ^ n •
        iteratedDeriv n (series c ℓ) (a : ℂ) =
      ((∑' i, taylorTerm c ℓ δ a (n, i) : ℝ) : ℂ) := by
  have ha' : σc < (a : ℂ).re := by rw [Complex.ofReal_re]; exact ha
  rw [iteratedDeriv_series hℓ hc hσ n ha', Complex.ofReal_tsum]
  have h1 : ((a - δ : ℝ) : ℂ) - (a : ℂ) = -(δ : ℂ) := by push_cast; ring
  rw [h1, series, smul_eq_mul, smul_eq_mul, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext i
  simp only [term, derivCoeff, taylorTerm]
  push_cast
  have h2 : (-(δ : ℂ)) ^ n * (-(ℓ i : ℂ)) ^ n = ((δ : ℂ) * (ℓ i : ℂ)) ^ n := by
    rw [← mul_pow, neg_mul_neg]
  calc (n.factorial : ℂ)⁻¹ * ((-(δ : ℂ)) ^ n *
        ((c i : ℂ) * (-(ℓ i : ℂ)) ^ n * Complex.exp (-(ℓ i : ℂ) * (a : ℂ))))
      = (n.factorial : ℂ)⁻¹ * ((c i : ℂ) * ((-(δ : ℂ)) ^ n * (-(ℓ i : ℂ)) ^ n) *
          Complex.exp (-(ℓ i : ℂ) * (a : ℂ))) := by ring
    _ = (c i : ℂ) * ((δ : ℂ) * (ℓ i : ℂ)) ^ n / (n.factorial : ℂ) *
          Complex.exp (-(ℓ i : ℂ) * (a : ℂ)) := by rw [h2]; ring

/-- **The Taylor step.** If `g` is holomorphic on the ball of radius `R` around the real
point `a`, to the right of the abscissa `σc`, and agrees with the series there, then the
series converges at `a - δ` for every `0 ≤ δ < R`. -/
theorem summableAt_sub_of_taylor (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σc a R δ : ℝ}
    (hσ : ∀ σ, σc < σ → SummableAt c ℓ σ) (ha : σc < a) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (a : ℂ) R))
    (hgD : ∀ s : ℂ, σc < s.re → s ∈ Metric.ball (a : ℂ) R → g s = series c ℓ s)
    (hδ0 : 0 ≤ δ) (hδ : δ < R) : SummableAt c ℓ (a - δ) := by
  have hR : 0 < R := lt_of_le_of_lt hδ0 hδ
  have hz : ((a - δ : ℝ) : ℂ) ∈ Metric.ball (a : ℂ) R := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show a - δ - a = -δ by ring, abs_neg, abs_of_nonneg hδ0]
    exact hδ
  have hT := Complex.hasSum_taylorSeries_on_ball hg hz
  have hev : g =ᶠ[𝓝 (a : ℂ)] series c ℓ := by
    have hmem : (a : ℂ) ∈ {s : ℂ | σc < s.re} ∩ Metric.ball (a : ℂ) R :=
      ⟨show σc < (a : ℂ).re by rw [Complex.ofReal_re]; exact ha, Metric.mem_ball_self hR⟩
    filter_upwards [((isOpen_halfPlane σc).inter Metric.isOpen_ball).mem_nhds hmem] with s hs
    exact hgD s hs.1 hs.2
  have hsum : HasSum (fun n : ℕ => ((∑' i, taylorTerm c ℓ δ a (n, i) : ℝ) : ℂ))
      (g ((a - δ : ℝ) : ℂ)) := by
    convert hT using 1
    funext n
    rw [hev.iteratedDeriv_eq n]
    exact (taylor_coeff_eq hℓ hc hσ ha δ n).symm
  have hsr : Summable fun n : ℕ => ∑' i, taylorTerm c ℓ δ a (n, i) :=
    Complex.summable_ofReal.mp hsum.summable
  have hcol : ∀ n : ℕ, Summable fun i => taylorTerm c ℓ δ a (n, i) := by
    intro n
    have h := (summableAt_mul_pow_of_forall hℓ hc hσ n ha).mul_left
      (δ ^ n / (n.factorial : ℝ))
    refine h.congr fun i => ?_
    simp only [taylorTerm]
    rw [mul_pow]
    ring
  have hprod : Summable (taylorTerm c ℓ δ a) :=
    (summable_prod_of_nonneg (taylorTerm_nonneg hℓ hc hδ0 a)).mpr ⟨hcol, hsr⟩
  have hswap : Summable (taylorTerm c ℓ δ a ∘ Equiv.prodComm ι ℕ) :=
    (Equiv.prodComm ι ℕ).summable_iff.mpr hprod
  have hrows := ((summable_prod_of_nonneg
    (fun p => taylorTerm_nonneg hℓ hc hδ0 a ((Equiv.prodComm ι ℕ) p))).mp hswap).2
  refine hrows.congr fun i => ?_
  have hexp : HasSum (fun n : ℕ => (δ * ℓ i) ^ n / (n.factorial : ℝ))
      (Real.exp (δ * ℓ i)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (δ * ℓ i)
  have h2 : HasSum (fun n : ℕ => taylorTerm c ℓ δ a ((Equiv.prodComm ι ℕ) (i, n)))
      (c i * Real.exp (δ * ℓ i) * Real.exp (-ℓ i * a)) := by
    have h3 := (hexp.mul_left (c i)).mul_right (Real.exp (-ℓ i * a))
    convert h3 using 1
    funext n
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, taylorTerm]
    ring
  rw [h2.tsum_eq, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Landau's theorem at the abscissa.** If the series converges to the right of `σc` and
agrees there with a function holomorphic on a disc around `σc`, it converges at some real
point to the left of `σc`. -/
theorem exists_summableAt_lt (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σc ε : ℝ}
    (hε : 0 < ε) (hσ : ∀ σ, σc < σ → SummableAt c ℓ σ) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (σc : ℂ) ε))
    (hgD : ∀ s : ℂ, σc < s.re → g s = series c ℓ s) :
    ∃ σ, σ < σc ∧ SummableAt c ℓ σ := by
  refine ⟨σc + ε / 4 - 3 * ε / 8, by linarith, ?_⟩
  refine summableAt_sub_of_taylor hℓ hc hσ (a := σc + ε / 4) (R := ε / 2) (by linarith)
    (hg.mono ?_) (fun s hs _ => hgD s hs) (by linarith) (by linarith)
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  have hd : dist ((σc + ε / 4 : ℝ) : ℂ) (σc : ℂ) = ε / 4 := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show σc + ε / 4 - σc = ε / 4 by ring, abs_of_pos (by linarith)]
  calc dist z (σc : ℂ) ≤ dist z ((σc + ε / 4 : ℝ) : ℂ) + dist ((σc + ε / 4 : ℝ) : ℂ) (σc : ℂ) :=
        dist_triangle _ _ _
    _ < ε := by rw [hd]; linarith

/-- The infimum argument: if no abscissa `σc > σ₀` of the series is final, then the series
converges at every real point to the right of `σ₀`. -/
theorem summableAt_of_abscissa (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σ₀ σ₁ : ℝ}
    (h₁ : SummableAt c ℓ σ₁)
    (hstep : ∀ σc : ℝ, σ₀ < σc → (∀ σ, σc < σ → SummableAt c ℓ σ) →
      ∃ σ, σ < σc ∧ SummableAt c ℓ σ) :
    ∀ σ, σ₀ < σ → SummableAt c ℓ σ := by
  intro σ₂ h₂
  by_contra hn
  have hlow : ∀ σ ∈ {σ : ℝ | SummableAt c ℓ σ}, σ₂ ≤ σ := by
    intro σ hσ
    by_contra hlt
    exact hn (SummableAt.mono hℓ hc hσ (le_of_lt (not_le.mp hlt)))
  have hne : ({σ : ℝ | SummableAt c ℓ σ}).Nonempty := ⟨σ₁, h₁⟩
  have hbdd : BddBelow {σ : ℝ | SummableAt c ℓ σ} := ⟨σ₂, hlow⟩
  have hσc : σ₂ ≤ sInf {σ : ℝ | SummableAt c ℓ σ} := le_csInf hne hlow
  have habove : ∀ σ, sInf {σ : ℝ | SummableAt c ℓ σ} < σ → SummableAt c ℓ σ := by
    intro σ hσ
    obtain ⟨σ', hσ'A, hσ'lt⟩ := exists_lt_of_csInf_lt hne hσ
    exact SummableAt.mono hℓ hc hσ'A hσ'lt.le
  obtain ⟨σ, hσlt, hσA⟩ := hstep _ (lt_of_lt_of_le h₂ hσc) habove
  exact absurd (csInf_le hbdd hσA) (not_le.mpr hσlt)

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

/-- **Landau's theorem** (Hardy–Riesz 1915, Theorem 10). Let `c i ≥ 0` and `ℓ i ≥ 0`. If the
general Dirichlet series `∑ c i exp (-ℓ i s)` converges at the real point `σ₁` and agrees,
on `σ₁ < Re s`, with a function holomorphic on `σ₀ < Re s`, then it converges at every real
`σ > σ₀`. -/
theorem summableAt_of_differentiableOn (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i)
    {σ₀ σ₁ : ℝ} (h₁ : SummableAt c ℓ σ₁) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {s : ℂ | σ₀ < s.re})
    (hgD : ∀ s : ℂ, σ₁ < s.re → g s = series c ℓ s) :
    ∀ σ, σ₀ < σ → SummableAt c ℓ σ := by
  refine summableAt_of_abscissa hℓ hc h₁ (fun σc hσc habove => ?_)
  have hsub : {s : ℂ | σc < s.re} ⊆ {s : ℂ | σ₀ < s.re} := fun s (hs : σc < s.re) =>
    show σ₀ < s.re from lt_trans hσc hs
  have heq := eqOn_halfPlane (hg.mono hsub) (differentiableOn_series hℓ hc habove) hgD
  exact exists_summableAt_lt hℓ hc (sub_pos.mpr hσc) habove
    (hg.mono ball_subset_halfPlane) (fun s hs => heq hs)

/-- **Landau's theorem for the exponential of the series.** Let `c i ≥ 0` and
`ℓ i ≥ ℓ₀ > 0`. If the series converges at the real point `σ₁` and `exp` of it agrees,
on `σ₁ < Re s`, with a function `L` holomorphic on `σ₀ < Re s`, then the series converges
at every real `σ > σ₀`. -/
theorem summableAt_of_exp (hc : ∀ i, 0 ≤ c i) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (hℓ₀le : ∀ i, ℓ₀ ≤ ℓ i) {σ₀ σ₁ : ℝ} (h₁ : SummableAt c ℓ σ₁) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {s : ℂ | σ₀ < s.re})
    (hLD : ∀ s : ℂ, σ₁ < s.re → L s = Complex.exp (series c ℓ s)) :
    ∀ σ, σ₀ < σ → SummableAt c ℓ σ := by
  have hℓ : ∀ i, 0 ≤ ℓ i := fun i => hℓ₀.le.trans (hℓ₀le i)
  refine summableAt_of_abscissa hℓ hc h₁ (fun σc hσc habove => ?_)
  have hD := differentiableOn_series hℓ hc habove
  have hsub : {s : ℂ | σc < s.re} ⊆ {s : ℂ | σ₀ < s.re} := fun s (hs : σc < s.re) =>
    show σ₀ < s.re from lt_trans hσc hs
  have heq : Set.EqOn L (fun s => Complex.exp (series c ℓ s)) {s : ℂ | σc < s.re} :=
    eqOn_halfPlane (hL.mono hsub) hD.cexp hLD
  have hσc' : (σc : ℂ) ∈ {s : ℂ | σ₀ < s.re} := by
    show σ₀ < (σc : ℂ).re
    rw [Complex.ofReal_re]
    exact hσc
  have hcont : ContinuousAt L (σc : ℂ) :=
    (hL.differentiableAt ((isOpen_halfPlane σ₀).mem_nhds hσc')).continuousAt
  -- `L` does not vanish at the abscissa
  have hLc : L (σc : ℂ) ≠ 0 := by
    have hlim : Tendsto (fun σ : ℝ => L (σ : ℂ)) (𝓝[>] σc) (𝓝 (L (σc : ℂ))) :=
      hcont.tendsto.comp
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hge : ∀ᶠ σ : ℝ in 𝓝[>] σc, 1 ≤ ‖L (σ : ℂ)‖ := by
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ' : (σ : ℂ) ∈ {s : ℂ | σc < s.re} := by
        show σc < (σ : ℂ).re
        rw [Complex.ofReal_re]
        exact hσ
      rw [heq hσ', Complex.norm_exp, series_ofReal, Complex.ofReal_re]
      exact Real.one_le_exp
        (tsum_nonneg fun i => mul_nonneg (hc i) (Real.exp_pos _).le)
    have h1 : 1 ≤ ‖L (σc : ℂ)‖ := ge_of_tendsto hlim.norm hge
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  -- a disc around the abscissa on which `L` is holomorphic and does not vanish
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0,
      Metric.ball (σc : ℂ) ε ⊆ {s : ℂ | σ₀ < s.re} ∩ {s : ℂ | L s ≠ 0} :=
    Metric.mem_nhds_iff.mp
      (Filter.inter_mem ((isOpen_halfPlane σ₀).mem_nhds hσc') (hcont.eventually_ne hLc))
  -- the logarithmic derivative `-L'/L`
  have hdL : DifferentiableOn ℂ (deriv L) {s : ℂ | σ₀ < s.re} := hL.deriv (isOpen_halfPlane σ₀)
  have hhd : DifferentiableOn ℂ (fun s => -(deriv L s / L s)) (Metric.ball (σc : ℂ) ε) := by
    intro z hz
    have hz' := hεsub hz
    have hsub' : Metric.ball (σc : ℂ) ε ⊆ {s : ℂ | σ₀ < s.re} := fun w hw => (hεsub hw).1
    exact (((hdL z hz'.1).mono hsub').div ((hL z hz'.1).mono hsub') hz'.2).neg
  have hhD : ∀ s : ℂ, σc < s.re →
      -(deriv L s / L s) = series (fun i => c i * ℓ i) ℓ s := by
    intro s hs
    have hev : L =ᶠ[𝓝 s] fun w => Complex.exp (series c ℓ w) := by
      filter_upwards [(isOpen_halfPlane σc).mem_nhds hs] with w hw
      exact heq hw
    have hderiv : deriv L s =
        Complex.exp (series c ℓ s) * -series (fun i => c i * ℓ i) ℓ s := by
      rw [hev.deriv_eq]
      exact (hasDerivAt_series hℓ hc habove hs).cexp.deriv
    rw [hderiv, heq hs, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _), neg_neg]
  have habove' : ∀ σ, σc < σ → SummableAt (fun i => c i * ℓ i) ℓ σ := by
    intro σ hσ
    have h := summableAt_mul_pow_of_forall hℓ hc habove 1 hσ
    simpa only [pow_one] using h
  obtain ⟨σ, hσlt, hσs⟩ := exists_summableAt_lt hℓ (fun i => mul_nonneg (hc i) (hℓ i)) hε
    habove' hhd hhD
  refine ⟨σ, hσlt, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hc i) (Real.exp_pos _).le)
    (fun i => ?_) (hσs.mul_left ℓ₀⁻¹)
  have h1 := mul_le_mul_of_nonneg_left (hℓ₀le i) (mul_nonneg (hc i) (Real.exp_pos (-ℓ i * σ)).le)
  show c i * Real.exp (-ℓ i * σ) ≤ ℓ₀⁻¹ * (c i * ℓ i * Real.exp (-ℓ i * σ))
  rw [← div_eq_inv_mul, le_div_iff₀ hℓ₀]
  nlinarith [h1]

end Langlands.GeneralDirichlet
