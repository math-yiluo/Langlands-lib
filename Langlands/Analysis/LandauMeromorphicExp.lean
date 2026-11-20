import Langlands.Analysis.LandauDirichlet

/-!
# Landau's theorem for a meromorphic continuation of the exponential

It suffices to rule out poles at real points above the proposed lower bound.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Metric

namespace Langlands.GeneralDirichlet

/-- A nonnegative Dirichlet series converging somewhere converges at every `σ > σ₀`
if its exponential has a meromorphic continuation to `σ₀ < Re s` with no real poles
there. -/
def MeromorphicExpLandauStatement : Prop :=
  ∀ {ι : Type*} {c ℓ : ι → ℝ}, (∀ i, 0 ≤ ℓ i) → (∀ i, 0 ≤ c i) →
    ∀ {σ₀ σ₁ : ℝ}, SummableAt c ℓ σ₁ →
    ∀ {L : ℂ → ℂ}, MeromorphicOn L {s : ℂ | σ₀ < s.re} →
      (∀ σ : ℝ, σ₀ < σ → 0 ≤ meromorphicOrderAt L (σ : ℂ)) →
      (∀ s : ℂ, σ₁ < s.re → L s = Complex.exp (series c ℓ s)) →
      ∀ σ : ℝ, σ₀ < σ → SummableAt c ℓ σ

private theorem eqOn_normalized_exp {ι : Type*} {c ℓ : ι → ℝ} {σ₀ σ₁ σc : ℝ}
    (hσc : σ₀ < σc) {L : ℂ → ℂ} (hL : MeromorphicOn L {s : ℂ | σ₀ < s.re})
    (hLD : ∀ s : ℂ, σ₁ < s.re → L s = Complex.exp (series c ℓ s))
    (hD : AnalyticOnNhd ℂ (fun s => Complex.exp (series c ℓ s)) {s : ℂ | σc < s.re}) :
    Set.EqOn (toMeromorphicNFOn L {s : ℂ | σ₀ < s.re})
      (fun s => Complex.exp (series c ℓ s)) {s : ℂ | σc < s.re} := by
  have hsub : {s : ℂ | σc < s.re} ⊆ {s : ℂ | σ₀ < s.re} := fun _ hs =>
    hσc.trans hs
  have hdif : MeromorphicOn (fun s => L s - Complex.exp (series c ℓ s))
      {s : ℂ | σc < s.re} := fun s hs => (hL s (hsub hs)).sub (hD s hs).meromorphicAt
  let a : ℝ := max σ₁ σc + 1
  have ha : σc < (a : ℂ).re := by rw [Complex.ofReal_re]; dsimp [a]; linarith [le_max_right σ₁ σc]
  have ha₁ : σ₁ < (a : ℂ).re := by rw [Complex.ofReal_re]; dsimp [a]; linarith [le_max_left σ₁ σc]
  have hz₀ : meromorphicOrderAt (fun s => L s - Complex.exp (series c ℓ s)) (a : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((isOpen_halfPlane σ₁).mem_nhds ha₁)] with s hs
    exact sub_eq_zero.mpr (hLD s hs)
  intro s hs
  have hz := hdif.meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt σc).isPreconnected ha hs hz₀
  have heq : L =ᶠ[𝓝[≠] s] fun z => Complex.exp (series c ℓ z) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp hz] with z hz
    exact sub_eq_zero.mp hz
  exact ((meromorphicNFOn_toMeromorphicNFOn L _ (hsub hs)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hD s hs).meromorphicNFAt).mp ((hL.toMeromorphicNFOn_eq_self_on_nhdsNE (hsub hs)).trans heq)
    |>.eq_of_nhds

/-- Landau's Taylor argument applied to a local logarithm of the normalized continuation. -/
theorem meromorphicExpLandau : MeromorphicExpLandauStatement := by
  intro ι c ℓ hℓ hc σ₀ σ₁ h₁ L hL horder hLD
  refine summableAt_of_abscissa hℓ hc h₁ (fun σc hσc habove => ?_)
  let G := toMeromorphicNFOn L {s : ℂ | σ₀ < s.re}
  have hD := (differentiableOn_series hℓ hc habove).analyticOnNhd (isOpen_halfPlane σc)
  have heq : Set.EqOn G (fun s => Complex.exp (series c ℓ s)) {s : ℂ | σc < s.re} :=
    eqOn_normalized_exp hσc hL hLD hD.cexp
  have hcenter : (σc : ℂ) ∈ {s : ℂ | σ₀ < s.re} := by simpa using hσc
  have hG : AnalyticAt ℂ G (σc : ℂ) :=
    (meromorphicNFOn_toMeromorphicNFOn L _ hcenter).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by simpa [G, meromorphicOrderAt_toMeromorphicNFOn hL hcenter] using horder σc hσc)
  have hGre : ContinuousAt (fun s => (G s).re) (σc : ℂ) :=
    Complex.continuous_re.continuousAt.comp hG.continuousAt
  have hpositive : 0 < (G (σc : ℂ)).re := by
    have hlim : Tendsto (fun t : ℝ => (G (t : ℂ)).re) (𝓝[>] σc) (𝓝 (G (σc : ℂ)).re) :=
      hGre.tendsto.comp
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hge : ∀ᶠ t : ℝ in 𝓝[>] σc, 1 ≤ (G (t : ℂ)).re := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (t : ℂ) ∈ {s : ℂ | σc < s.re} := by simpa using ht
      simp only [heq ht', series_ofReal, Complex.exp_ofReal_re]
      exact Real.one_le_exp (tsum_nonneg fun i => mul_nonneg (hc i) (Real.exp_pos _).le)
    exact zero_lt_one.trans_le (ge_of_tendsto hlim hge)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hG.eventually_analyticAt.and (hGre.tendsto.eventually (eventually_gt_nhds hpositive)))
  let a : ℝ := σc + ε / 4
  have ha : σc < a := by dsimp [a]; linarith
  have ha' : (a : ℂ) ∈ {s : ℂ | σc < s.re} := by simpa using ha
  have hdist : dist (a : ℂ) (σc : ℂ) = ε / 4 := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show a - σc = ε / 4 by dsimp [a]; ring, abs_of_pos (by linarith)]
  have haBall : (a : ℂ) ∈ Metric.ball (σc : ℂ) ε := by
    rw [Metric.mem_ball, hdist]
    linarith
  have hlog : AnalyticOnNhd ℂ (fun s => Complex.log (G s)) (Metric.ball (σc : ℂ) ε) :=
    fun s hs => (hball hs).1.clog (Complex.mem_slitPlane_iff.mpr (.inl (hball hs).2))
  have heqLog : Set.EqOn (fun s => Complex.log (G s)) (series c ℓ)
      (Metric.ball (σc : ℂ) ε ∩ {s : ℂ | σc < s.re}) := by
    refine (hlog.mono Set.inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      (hD.mono Set.inter_subset_right)
      ((convex_ball (σc : ℂ) ε).inter (convex_halfSpace_re_gt σc)).isPreconnected
      ⟨haBall, ha'⟩ ?_
    have him : (series c ℓ (a : ℂ)).im = 0 := by rw [series_ofReal, Complex.ofReal_im]
    have hnear : ∀ᶠ s in 𝓝 (a : ℂ), (series c ℓ s).im ∈ Set.Ioo (-Real.pi) Real.pi :=
      (Complex.continuous_im.continuousAt.comp (hD _ ha').continuousAt).tendsto.eventually
        (isOpen_Ioo.mem_nhds (by
          simp only [Function.comp_apply, him]
          exact ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩))
    filter_upwards [hnear, (isOpen_halfPlane σc).mem_nhds ha'] with s hs hs'
    rw [heq hs', Complex.log_exp hs.1 hs.2.le]
  have hsub : Metric.ball (a : ℂ) (ε / 2) ⊆ Metric.ball (σc : ℂ) ε :=
    Metric.ball_subset_ball' (by rw [hdist]; linarith)
  refine ⟨a - 3 * ε / 8, by dsimp [a]; linarith, ?_⟩
  exact summableAt_sub_of_taylor hℓ hc habove ha (R := ε / 2) (g := fun s => Complex.log (G s))
    (hlog.differentiableOn.mono hsub) (fun s hs hd => heqLog ⟨hsub hd, hs⟩)
    (by linarith) (by linarith)

end Langlands.GeneralDirichlet
