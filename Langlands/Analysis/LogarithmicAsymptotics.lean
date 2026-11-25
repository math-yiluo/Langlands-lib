import Langlands.MathlibBase

/-!
# Logarithms of meromorphic functions near a point of the line `Re s = 1`

Let `f` be meromorphic at `z₀ = 1 + iθ` with order `n`, and let `l` be a continuous logarithm
of `σ ↦ f (σ + iθ)` on an interval `(1, a)`. Then `l σ / log (1/(σ - 1)) → -n` as `σ → 1⁺`.
This is the analytic step of the proof of Jacquet–Shalika II, Theorem (4.1).

The proof writes `f z = (z - z₀)^n g z` with `g` analytic and nonzero at `z₀`. Then
`l σ - n log (σ - 1) - log (g (σ + iθ) / g z₀)` is a continuous function whose exponential is
constant, so it is constant on `(1, b)` for some `b > 1`.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology Complex

namespace Langlands.LogarithmicAsymptotics

/-- A continuous integer-valued real function on a preconnected set is constant. -/
private theorem eq_of_intValued {s : Set ℝ} (hs : IsPreconnected s) {g : ℝ → ℝ}
    (hg : ContinuousOn g s)
    (hint : ∀ x ∈ s, ∃ n : ℤ, g x = n) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) : g x = g y := by
  -- the case `g x < g y`; the other case is symmetric
  have key : ∀ {x y : ℝ}, x ∈ s → y ∈ s → g x < g y → False := by
    intro x y hx hy hlt
    obtain ⟨m, hm⟩ := hint x hx
    obtain ⟨k, hk⟩ := hint y hy
    have hmk : m < k := by exact_mod_cast (show (m : ℝ) < k by rw [← hm, ← hk]; exact hlt)
    have hmk' : (m : ℝ) + 1 ≤ k := by exact_mod_cast hmk
    have hmem : g x + 1 / 2 ∈ Set.Icc (g x) (g y) := by
      constructor
      · linarith
      · rw [hm, hk]; linarith
    obtain ⟨z, hz, hgz⟩ := hs.intermediate_value hx hy hg hmem
    obtain ⟨j, hj⟩ := hint z hz
    rw [hj, hm] at hgz
    have h2 : ((2 * (j - m) : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h4 : (2 * (j - m) : ℤ) = 1 := by exact_mod_cast h2
    omega
  rcases lt_trichotomy (g x) (g y) with hlt | heq | hgt
  · exact (key hx hy hlt).elim
  · exact heq
  · exact (key hy hx hgt).elim

/-- `log (1/(σ - 1)) → +∞` as `σ → 1⁺`. -/
private theorem tendsto_log_inv_sub_one :
    Tendsto (fun σ : ℝ => Real.log (1 / (σ - 1))) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    have hc : Tendsto (fun σ : ℝ => σ - 1) (𝓝 1) (𝓝 0) := by
      have := (continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ)
      simpa using this
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hσ))
  have h2 : Tendsto (fun σ : ℝ => 1 / (σ - 1)) (𝓝[>] 1) atTop := by
    have := tendsto_inv_nhdsGT_zero.comp h1
    simpa [Function.comp_def, one_div] using this
  exact Real.tendsto_log_atTop.comp h2

/-- **Logarithmic asymptotics at a point of `Re s = 1`.** Let `f` be meromorphic of order `n`
at `1 + iθ`, and let `l` be continuous on `(1, a)` with `exp (l σ) = f (σ + iθ)` there. Then
`l σ / log (1/(σ - 1)) → -n` as `σ → 1⁺`. -/
def BoundaryLogarithmAsymptoticsStatement : Prop :=
  ∀ {f : ℂ → ℂ} {θ : ℝ} {n : ℤ}, MeromorphicAt f (1 + θ * I) →
    meromorphicOrderAt f (1 + θ * I) = n →
    ∀ {l : ℝ → ℂ} {a : ℝ}, 1 < a → ContinuousOn l (Set.Ioo 1 a) →
      (∀ σ ∈ Set.Ioo 1 a, Complex.exp (l σ) = f (σ + θ * I)) →
      Tendsto (fun σ : ℝ => l σ / (Real.log (1 / (σ - 1)) : ℂ)) (𝓝[>] 1) (𝓝 (-n : ℂ))

/-- A continuous logarithm has normalized boundary limit given by the negative
of the meromorphic order. -/
theorem tendsto_div_log_of_meromorphicOrderAt : BoundaryLogarithmAsymptoticsStatement := by
  intro f θ n hf hn l a ha hl hexp
  set z₀ : ℂ := 1 + θ * I with hz₀
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn
  -- the path `σ ↦ σ + iθ`
  set γ : ℝ → ℂ := fun σ => (σ : ℂ) + θ * I with hγ
  have hγc : Continuous γ := by fun_prop
  have hγ1 : γ 1 = z₀ := by simp [hγ, hz₀]
  have hγsub : ∀ σ : ℝ, γ σ - z₀ = ((σ - 1 : ℝ) : ℂ) := by
    intro σ; simp only [hγ, hz₀]; push_cast; ring
  have hγlim : Tendsto γ (𝓝[>] 1) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [← hγ1]; exact (hγc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      intro h
      have h' := hγsub σ
      rw [show γ σ = z₀ from h, sub_self] at h'
      have : (σ - 1 : ℝ) = 0 := by exact_mod_cast h'.symm
      have hσ' : (1 : ℝ) < σ := hσ
      linarith
  -- `g ∘ γ` is continuous at `1`, with value `g z₀ ≠ 0`
  have hgγ : ContinuousAt (fun σ : ℝ => g (γ σ)) 1 := by
    have := hg.continuousAt
    rw [← hγ1] at this
    exact this.comp hγc.continuousAt
  set q : ℝ → ℂ := fun σ => g (γ σ) / g z₀ with hq
  have hqc : ContinuousAt q 1 := hgγ.div_const _
  have hq1 : q 1 = 1 := by simp [hq, hγ1, div_self hg0]
  -- eventual properties near `1⁺`
  have ev1 : ∀ᶠ σ in 𝓝[>] (1 : ℝ), f (γ σ) = (γ σ - z₀) ^ n • g (γ σ) := hγlim.eventually hfg
  have ev2 : ∀ᶠ σ in 𝓝[>] (1 : ℝ), ‖q σ - 1‖ < 1 := by
    have h : Tendsto (fun σ => ‖q σ - 1‖) (𝓝 1) (𝓝 ‖q 1 - 1‖) :=
      ((hqc.sub (continuousAt_const (y := (1 : ℂ)))).norm).tendsto
    rw [hq1, sub_self, norm_zero] at h
    exact (h.eventually (gt_mem_nhds one_pos)).filter_mono nhdsWithin_le_nhds
  have ev3 : ∀ᶠ σ in 𝓝[>] (1 : ℝ), σ < min a 2 :=
    (gt_mem_nhds (lt_min ha one_lt_two)).filter_mono nhdsWithin_le_nhds
  have ev4 : ∀ᶠ σ in 𝓝[>] (1 : ℝ), AnalyticAt ℂ g (γ σ) := by
    have h := hγc.continuousAt.tendsto (x := (1 : ℝ))
    rw [hγ1] at h
    exact (h.eventually hg.eventually_analyticAt).filter_mono nhdsWithin_le_nhds
  obtain ⟨b, hb1, hbsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (ev1.and (ev2.and (ev3.and ev4)))
  have hb1' : (1 : ℝ) < b := hb1
  have hfb : ∀ σ ∈ Set.Ioo 1 b, f (γ σ) = (γ σ - z₀) ^ n • g (γ σ) := fun σ hσ => (hbsub hσ).1
  have hqb : ∀ σ ∈ Set.Ioo 1 b, ‖q σ - 1‖ < 1 := fun σ hσ => (hbsub hσ).2.1
  have hab : ∀ σ ∈ Set.Ioo 1 b, σ < min a 2 := fun σ hσ => (hbsub hσ).2.2.1
  have hgb : ∀ σ ∈ Set.Ioo 1 b, AnalyticAt ℂ g (γ σ) := fun σ hσ => (hbsub hσ).2.2.2
  have hsuba : ∀ σ ∈ Set.Ioo 1 b, σ ∈ Set.Ioo 1 a :=
    fun σ hσ => ⟨hσ.1, (hab σ hσ).trans_le (min_le_left _ _)⟩
  have hlt2 : ∀ σ ∈ Set.Ioo 1 b, σ < 2 := fun σ hσ => (hab σ hσ).trans_le (min_le_right _ _)
  -- `q σ` lies in the slit plane
  have hqslit : ∀ σ ∈ Set.Ioo 1 b, q σ ∈ slitPlane := by
    intro σ hσ
    have h := mem_slitPlane_of_norm_lt_one (hqb σ hσ)
    rwa [add_sub_cancel] at h
  have hqne : ∀ σ ∈ Set.Ioo 1 b, q σ ≠ 0 := fun σ hσ => slitPlane_ne_zero (hqslit σ hσ)
  -- the corrected logarithm
  set L₀ : ℂ := Complex.log (g z₀) with hL₀
  set h : ℝ → ℂ := fun σ =>
    l σ - (n : ℂ) * ((Real.log (σ - 1) : ℝ) : ℂ) - Complex.log (q σ) with hh
  have hexph : ∀ σ ∈ Set.Ioo 1 b, Complex.exp (h σ) = Complex.exp L₀ := by
    intro σ hσ
    have hpos : 0 < σ - 1 := sub_pos.mpr hσ.1
    have hx : ((σ - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hpow : Complex.exp ((n : ℂ) * ((Real.log (σ - 1) : ℝ) : ℂ)) = ((σ - 1 : ℝ) : ℂ) ^ n := by
      rw [Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hpos]
    have hgne : g (γ σ) ≠ 0 := by
      intro h0
      apply hqne σ hσ
      simp [hq, h0]
    rw [hL₀, Complex.exp_log hg0, hh]
    simp only
    rw [Complex.exp_sub, Complex.exp_sub, hpow, Complex.exp_log (hqne σ hσ),
      hexp σ (hsuba σ hσ), hfb σ hσ, hγsub, smul_eq_mul, hq]
    simp only
    field_simp
  -- the corrected logarithm is constant
  have hcont_h : ContinuousOn h (Set.Ioo 1 b) := by
    have h1 : ContinuousOn l (Set.Ioo 1 b) := hl.mono fun σ hσ => hsuba σ hσ
    have h2 : ContinuousOn (fun σ : ℝ => (n : ℂ) * ((Real.log (σ - 1) : ℝ) : ℂ))
        (Set.Ioo 1 b) := by
      apply ContinuousOn.mul continuousOn_const
      apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro σ hσ
      exact (sub_pos.mpr hσ.1).ne'
    have h3 : ContinuousOn (fun σ => Complex.log (q σ)) (Set.Ioo 1 b) := by
      intro σ hσ
      apply ContinuousAt.continuousWithinAt
      apply (continuousAt_clog (hqslit σ hσ)).comp
      exact ((hgb σ hσ).continuousAt.comp hγc.continuousAt).div_const _
    exact (h1.sub h2).sub h3
  set k : ℝ → ℝ := fun σ => (h σ - L₀).im / (2 * Real.pi) with hk
  have hkint : ∀ σ ∈ Set.Ioo 1 b, ∃ m : ℤ, k σ = m := by
    intro σ hσ
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexph σ hσ)
    refine ⟨m, ?_⟩
    rw [hk]
    simp only
    rw [hm, add_sub_cancel_left]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]
    field_simp
    ring
  have hkc : ContinuousOn k (Set.Ioo 1 b) :=
    ((Complex.continuous_im.comp_continuousOn (hcont_h.sub continuousOn_const))).div_const _
  have hhk : ∀ σ ∈ Set.Ioo 1 b, h σ = L₀ + ((k σ : ℝ) : ℂ) * (2 * Real.pi * I) := by
    intro σ hσ
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexph σ hσ)
    obtain ⟨m', hm'⟩ := hkint σ hσ
    have hmm : (m' : ℝ) = m := by
      rw [← hm', hk]
      simp only
      rw [hm, add_sub_cancel_left]
      simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
        Complex.im_ofNat]
      field_simp
      ring
    rw [hm, hm', hmm]
    push_cast
    ring
  set c : ℝ := (1 + b) / 2 with hc
  have hcmem : c ∈ Set.Ioo 1 b := ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩
  have hhc : ∀ σ ∈ Set.Ioo 1 b, h σ = h c := by
    intro σ hσ
    rw [hhk σ hσ, hhk c hcmem,
      eq_of_intValued isPreconnected_Ioo hkc hkint hσ hcmem]
  -- the explicit form of the quotient
  set Lg : ℝ → ℝ := fun σ => Real.log (1 / (σ - 1)) with hLg
  have hform : ∀ σ ∈ Set.Ioo 1 b, l σ / (Lg σ : ℂ) =
      -(n : ℂ) + (h c + Complex.log (q σ)) * ((Lg σ : ℝ) : ℂ)⁻¹ := by
    intro σ hσ
    have hpos : 0 < σ - 1 := sub_pos.mpr hσ.1
    have hlt1 : σ - 1 < 1 := by linarith [hlt2 σ hσ]
    have hlog : Real.log (σ - 1) < 0 := Real.log_neg hpos hlt1
    have hLgeq : Lg σ = -Real.log (σ - 1) := by
      rw [hLg]; simp only; rw [one_div, Real.log_inv]
    have hLne : ((Real.log (σ - 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog.ne
    have hl : l σ = h c + (n : ℂ) * ((Real.log (σ - 1) : ℝ) : ℂ) + Complex.log (q σ) := by
      rw [← hhc σ hσ, hh]
      ring
    rw [hl, hLgeq, Complex.ofReal_neg]
    generalize ((Real.log (σ - 1) : ℝ) : ℂ) = L at hLne ⊢
    field_simp
    ring
  -- limits
  have hlimq : Tendsto (fun σ : ℝ => h c + Complex.log (q σ)) (𝓝[>] 1) (𝓝 (h c)) := by
    have h1 : ContinuousAt (fun σ => Complex.log (q σ)) 1 := by
      apply (continuousAt_clog _).comp hqc
      rw [hq1]; exact one_mem_slitPlane
    have h2 := h1.tendsto
    rw [hq1, Complex.log_one] at h2
    have h3 : Tendsto (fun σ : ℝ => h c + Complex.log (q σ)) (𝓝[>] 1) (𝓝 (h c + 0)) :=
      (tendsto_const_nhds (x := h c)).add (h2.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1)))
    simpa using h3
  have hliminv : Tendsto (fun σ : ℝ => ((Lg σ : ℝ) : ℂ)⁻¹) (𝓝[>] 1) (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ => (Lg σ)⁻¹) (𝓝[>] 1) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_log_inv_sub_one
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    simpa [Function.comp_def] using h2
  have hlim : Tendsto (fun σ : ℝ => -(n : ℂ) + (h c + Complex.log (q σ)) * ((Lg σ : ℝ) : ℂ)⁻¹)
      (𝓝[>] 1) (𝓝 (-n : ℂ)) := by
    have h1 := tendsto_const_nhds (x := -(n : ℂ)) |>.add (hlimq.mul hliminv)
    simpa using h1
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hb1'] with σ hσ
  exact (hform σ hσ).symm

end Langlands.LogarithmicAsymptotics
