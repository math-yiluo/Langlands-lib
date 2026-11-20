import Mathlib

/-! # Approximation lemmas for bounded wave packets

Analytic lemmas used in the proof of Lapid 2011, Lemma 10 (p.329): approximation of bounded
measurable coefficients by smooth ones with support in a fixed compact set (step (1)–(4) of
Lapid's proof), the passage from an `L²`-Cauchy sequence with a pointwise limit to `L²`
convergence (the identification `F = Θ_φ`), and the continuity of the `L²` inner product. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

set_option autoImplicit false

namespace Langlands.Global.BoundedWavePacket

/-! ### Clamping -/

/-- Clamping a real number to `[-C, C]` moves it no farther from any point of `[-C, C]`. -/
theorem abs_clamp_sub_le {C a b : ℝ} (hb : |b| ≤ C) :
    |max (-C) (min C a) - b| ≤ |a - b| := by
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  rcases le_or_gt a (-C) with h | h
  · have e : max (-C) (min C a) = -C := by
      rw [max_eq_left]; exact (min_le_right _ _).trans h
    rw [e, abs_of_nonpos (by linarith : -C - b ≤ 0), abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · rcases le_or_gt a C with h' | h'
    · have e : max (-C) (min C a) = a := by rw [min_eq_right h', max_eq_right h.le]
      rw [e]
    · have e : max (-C) (min C a) = C := by
        rw [min_eq_left h'.le, max_eq_right (by linarith)]
      rw [e, abs_of_nonneg (by linarith : 0 ≤ C - b), abs_of_nonneg (by linarith : 0 ≤ a - b)]
      linarith

theorem abs_clamp_le {C a : ℝ} (hC : 0 ≤ C) : |max (-C) (min C a)| ≤ C := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- The clamp of a complex number to the square `[-C, C] × [-C, C]`. -/
def clampComplex (C : ℝ) (z : ℂ) : ℂ :=
  ((max (-C) (min C z.re) : ℝ) : ℂ) + ((max (-C) (min C z.im) : ℝ) : ℂ) * Complex.I

theorem continuous_clampComplex (C : ℝ) : Continuous (clampComplex C) := by
  unfold clampComplex
  fun_prop

@[simp] theorem clampComplex_re (C : ℝ) (z : ℂ) :
    (clampComplex C z).re = max (-C) (min C z.re) := by
  simp [clampComplex]

@[simp] theorem clampComplex_im (C : ℝ) (z : ℂ) :
    (clampComplex C z).im = max (-C) (min C z.im) := by
  simp [clampComplex]

theorem clampComplex_zero {C : ℝ} (hC : 0 ≤ C) : clampComplex C 0 = 0 := by
  apply Complex.ext <;> simp [hC]

theorem norm_clampComplex_le {C : ℝ} (hC : 0 ≤ C) (z : ℂ) : ‖clampComplex C z‖ ≤ 2 * C := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [clampComplex_re, clampComplex_im]
  linarith [abs_clamp_le (a := z.re) hC, abs_clamp_le (a := z.im) hC]

theorem norm_clampComplex_sub_le {C : ℝ} {w : ℂ} (hw : ‖w‖ ≤ C) (z : ℂ) :
    ‖clampComplex C z - w‖ ≤ 2 * ‖z - w‖ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, clampComplex_re, clampComplex_im]
  have h1 := abs_clamp_sub_le (a := z.re) ((Complex.abs_re_le_norm w).trans hw)
  have h2 := abs_clamp_sub_le (a := z.im) ((Complex.abs_im_le_norm w).trans hw)
  have h3 : |z.re - w.re| ≤ ‖z - w‖ := by
    simpa using Complex.abs_re_le_norm (z - w)
  have h4 : |z.im - w.im| ≤ ‖z - w‖ := by
    simpa using Complex.abs_im_le_norm (z - w)
  linarith

/-! ### Smooth approximation -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A bounded measurable function `f` vanishing outside a compact set `S ⊆ interior N` is
approximated in `L¹(ν)`, for a finite measure `ν`, by smooth functions vanishing outside `N`
and bounded by `2C + 1`. -/
theorem exists_smooth_integral_norm_sub_le (ν : Measure E) [IsFiniteMeasure ν]
    {S N : Set E} (hS : IsCompact S) (hSN : S ⊆ interior N)
    {f : E → ℂ} {C : ℝ} (hf : Measurable f) (hC : ∀ x, ‖f x‖ ≤ C)
    (hfS : ∀ x ∉ S, f x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℂ, ContDiff ℝ ∞ g ∧ (∀ x ∉ N, g x = 0) ∧ (∀ x, ‖g x‖ ≤ 2 * C + 1) ∧
      Integrable (g - f) ν ∧ ∫ x, ‖g x - f x‖ ∂ν ≤ ε := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  obtain ⟨g₀, hg₀s, hg₀e, hg₀c, hg₀i⟩ :=
    hfi.exists_hasCompactSupport_integral_sub_le (ε := ε / 4) (by positivity)
  set g₁ : E → ℂ := fun x => clampComplex C (g₀ x) with hg₁
  have hg₁c : Continuous g₁ := (continuous_clampComplex C).comp hg₀c
  have hg₁s : HasCompactSupport g₁ := hg₀s.comp_left (clampComplex_zero hC0)
  have hg₁u : UniformContinuous g₁ := hg₁s.uniformContinuous_of_continuous hg₁c
  set t : ℝ := ν.real univ with ht
  have ht0 : 0 ≤ t := measureReal_nonneg
  set δ : ℝ := min 1 (ε / (2 * (t + 1))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδt : δ * t ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * (t + 1)) := min_le_right _ _
    calc δ * t ≤ ε / (2 * (t + 1)) * t := mul_le_mul_of_nonneg_right h1 ht0
      _ ≤ ε / (2 * (t + 1)) * (t + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 2 := by field_simp
  obtain ⟨g₂, hg₂c, hg₂d⟩ := hg₁u.exists_contDiff_dist_le hδ0
  obtain ⟨χ, hχc, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) isOpen_interior hS.isClosed hSN
  have hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x => hχr (mem_range_self x)
  refine ⟨fun x => (χ x : ℂ) * g₂ x, ?_, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hχc).mul hg₂c
  · intro x hx
    have : χ x = 0 := by
      by_contra h
      have hx' : x ∈ Function.support χ := h
      rw [hχs] at hx'
      exact hx (interior_subset hx')
    simp [this]
  · intro x
    have h2 : ‖g₂ x‖ ≤ 2 * C + 1 := by
      have := hg₂d x
      rw [dist_eq_norm] at this
      have h3 : ‖g₁ x‖ ≤ 2 * C := norm_clampComplex_le hC0 _
      calc ‖g₂ x‖ ≤ ‖g₂ x - g₁ x‖ + ‖g₁ x‖ := norm_le_norm_sub_add _ _
        _ ≤ 2 * C + 1 := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ01 x).1]
    calc χ x * ‖g₂ x‖ ≤ 1 * ‖g₂ x‖ :=
          mul_le_mul_of_nonneg_right (hχ01 x).2 (norm_nonneg _)
      _ ≤ 2 * C + 1 := by linarith
  -- the pointwise error bound
  have hpt : ∀ x, ‖(χ x : ℂ) * g₂ x - f x‖ ≤ δ + 2 * ‖g₀ x - f x‖ := by
    intro x
    have hfx : f x = (χ x : ℂ) * f x := by
      by_cases hx : x ∈ S
      · rw [(hχ1 x).1 hx]; simp
      · simp [hfS x hx]
    have e1 : (χ x : ℂ) * g₂ x - f x = (χ x : ℂ) * (g₂ x - f x) := by
      conv_lhs => rw [hfx]
      ring
    rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ01 x).1]
    have h1 : ‖g₂ x - f x‖ ≤ δ + 2 * ‖g₀ x - f x‖ := by
      have hd := hg₂d x
      rw [dist_eq_norm] at hd
      have hc := norm_clampComplex_sub_le (hC x) (g₀ x)
      calc ‖g₂ x - f x‖ ≤ ‖g₂ x - g₁ x‖ + ‖g₁ x - f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ + 2 * ‖g₀ x - f x‖ := by
          have : g₁ x = clampComplex C (g₀ x) := rfl
          rw [this]; linarith
    calc χ x * ‖g₂ x - f x‖ ≤ 1 * ‖g₂ x - f x‖ :=
          mul_le_mul_of_nonneg_right (hχ01 x).2 (norm_nonneg _)
      _ ≤ δ + 2 * ‖g₀ x - f x‖ := by linarith
  have hgm : Measurable (fun x => (χ x : ℂ) * g₂ x) :=
    ((Complex.continuous_ofReal.comp hχc.continuous).mul hg₂c.continuous).measurable
  have hdiffi : Integrable ((fun x => (χ x : ℂ) * g₂ x) - f) ν := by
    refine Integrable.of_bound (hgm.sub hf).aestronglyMeasurable (2 * C + 1 + C) (ae_of_all _ ?_)
    intro x
    simp only [Pi.sub_apply]
    have h2 : ‖(χ x : ℂ) * g₂ x‖ ≤ 2 * C + 1 := by
      have hd := hg₂d x
      rw [dist_eq_norm] at hd
      have h3 : ‖g₁ x‖ ≤ 2 * C := norm_clampComplex_le hC0 _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ01 x).1]
      calc χ x * ‖g₂ x‖ ≤ 1 * ‖g₂ x‖ :=
            mul_le_mul_of_nonneg_right (hχ01 x).2 (norm_nonneg _)
        _ ≤ ‖g₂ x - g₁ x‖ + ‖g₁ x‖ := by rw [one_mul]; exact norm_le_norm_sub_add _ _
        _ ≤ 2 * C + 1 := by linarith
    calc ‖(χ x : ℂ) * g₂ x - f x‖ ≤ ‖(χ x : ℂ) * g₂ x‖ + ‖f x‖ := norm_sub_le _ _
      _ ≤ 2 * C + 1 + C := by linarith [hC x]
  refine ⟨hdiffi, ?_⟩
  have hbi : Integrable (fun x => δ + 2 * ‖g₀ x - f x‖) ν :=
    (integrable_const δ).add ((hg₀i.sub hfi).norm.const_mul 2)
  calc ∫ x, ‖(χ x : ℂ) * g₂ x - f x‖ ∂ν ≤ ∫ x, (δ + 2 * ‖g₀ x - f x‖) ∂ν :=
        integral_mono hdiffi.norm hbi hpt
    _ = δ * t + 2 * ∫ x, ‖f x - g₀ x‖ ∂ν := by
        have hI : Integrable (fun x => 2 * ‖g₀ x - f x‖) ν := (hg₀i.sub hfi).norm.const_mul 2
        rw [integral_add (integrable_const δ) hI, integral_const, integral_const_mul]
        simp only [smul_eq_mul, ht]
        rw [mul_comm]
        congr 2
        exact integral_congr_ae (ae_of_all _ fun x => norm_sub_rev _ _)
    _ ≤ ε / 2 + 2 * (ε / 4) := by linarith
    _ = ε := by ring

/-- Sequence version of `exists_smooth_integral_norm_sub_le`, with convergence almost
everywhere. -/
theorem exists_seq_smooth_tendsto_ae (ν : Measure E) [IsFiniteMeasure ν]
    {S N : Set E} (hS : IsCompact S) (hSN : S ⊆ interior N)
    {f : E → ℂ} {C : ℝ} (hf : Measurable f) (hC : ∀ x, ‖f x‖ ≤ C)
    (hfS : ∀ x ∉ S, f x = 0) :
    ∃ g : ℕ → E → ℂ, (∀ m, ContDiff ℝ ∞ (g m)) ∧ (∀ m x, x ∉ N → g m x = 0) ∧
      (∀ m x, ‖g m x‖ ≤ 2 * C + 1) ∧
      ∀ᵐ x ∂ν, Tendsto (fun m => g m x) atTop (𝓝 (f x)) := by
  have key : ∀ m : ℕ, ∃ g : E → ℂ, ContDiff ℝ ∞ g ∧ (∀ x ∉ N, g x = 0) ∧
      (∀ x, ‖g x‖ ≤ 2 * C + 1) ∧ Integrable (g - f) ν ∧
      ∫ x, ‖g x - f x‖ ∂ν ≤ 1 / ((m : ℝ) + 1) := fun m =>
    exists_smooth_integral_norm_sub_le ν hS hSN hf hC hfS (by positivity)
  choose g hgc hgN hgb hgi hge using key
  have hL1 : Tendsto (fun m => eLpNorm (g m - f) 1 ν) atTop (𝓝 0) := by
    have e : ∀ m, eLpNorm (g m - f) 1 ν = ENNReal.ofReal (∫ x, ‖g m x - f x‖ ∂ν) := by
      intro m
      rw [eLpNorm_one_eq_lintegral_enorm (hgi m).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hgi m)]
      rfl
    simp_rw [e]
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    refine squeeze_zero (fun m => integral_nonneg fun x => norm_nonneg _) hge ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hL1).exists_seq_tendsto_ae
  exact ⟨fun m => g (ns m), fun m => hgc _, fun m => hgN _, fun m => hgb _, hns⟩

/-! ### Dominated convergence for bounded functions vanishing outside a set -/

section Dominated

variable {α : Type*} [MeasurableSpace α] {σ : Measure α}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ G] in
theorem aestronglyMeasurable_of_restrict_of_zero_off {N : Set α} (hN : MeasurableSet N)
    {F : α → G} (hF : AEStronglyMeasurable F (σ.restrict N)) (h0 : ∀ x ∉ N, F x = 0) :
    AEStronglyMeasurable F σ := by
  have e : F = N.indicator F := by
    funext x
    by_cases hx : x ∈ N
    · simp [hx]
    · simp [hx, h0 x hx]
  rw [e]
  exact (aestronglyMeasurable_indicator_iff hN).2 hF

omit [NormedSpace ℝ G] in
theorem integrable_of_bdd_of_zero_off {N : Set α} (hN : MeasurableSet N) (hσN : σ N < ⊤)
    {F : α → G} {B : ℝ} (hF : AEStronglyMeasurable F σ) (hFb : ∀ x, ‖F x‖ ≤ B)
    (h0 : ∀ x ∉ N, F x = 0) : Integrable F σ := by
  have e : F = N.indicator F := by
    funext x
    by_cases hx : x ∈ N
    · simp [hx]
    · simp [hx, h0 x hx]
  rw [e, integrable_indicator_iff hN]
  have : IsFiniteMeasure (σ.restrict N) := isFiniteMeasure_restrict.2 hσN.ne
  exact Integrable.of_bound hF.restrict B (ae_of_all _ hFb)

theorem tendsto_integral_of_bdd_of_zero_off {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {N : Set α} (hN : MeasurableSet N) (hσN : σ N < ⊤) {F : ι → α → G} {F₀ : α → G} {B : ℝ}
    (hFm : ∀ i, AEStronglyMeasurable (F i) σ) (hFb : ∀ i x, ‖F i x‖ ≤ B)
    (hF0 : ∀ i x, x ∉ N → F i x = 0)
    (hlim : ∀ᵐ x ∂σ, Tendsto (fun i => F i x) l (𝓝 (F₀ x))) :
    Tendsto (fun i => ∫ x, F i x ∂σ) l (𝓝 (∫ x, F₀ x ∂σ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (N.indicator fun _ => B)
    (Eventually.of_forall hFm) (Eventually.of_forall fun i => ae_of_all _ fun x => ?_) ?_ hlim
  · by_cases hx : x ∈ N
    · simpa [hx] using hFb i x
    · simp [hx, hF0 i x hx]
  · rw [integrable_indicator_iff hN]
    exact integrableOn_const hσN.ne

end Dominated

/-! ### `L²` limits -/

section L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem eLpNorm_two_eq_ofReal_sqrt {u : α → ℂ} (hu : MemLp u 2 μ) :
    eLpNorm u 2 μ = ENNReal.ofReal ((∫ x, ‖u x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) := by
  rw [hu.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  congr 3
  funext x
  exact Real.rpow_natCast _ 2

/-- An `L²`-Cauchy sequence with a pointwise limit converges to it in `L²`. -/
theorem memLp_two_and_tendsto_of_cauchy {f : ℕ → α → ℂ} {h : α → ℂ}
    (hf : ∀ m, MemLp (f m) 2 μ) (hlim : ∀ x, Tendsto (fun m => f m x) atTop (𝓝 (h x)))
    (hC : Tendsto (fun p : ℕ × ℕ => ∫ x, ‖f p.1 x - f p.2 x‖ ^ 2 ∂μ) (atTop ×ˢ atTop) (𝓝 0)) :
    MemLp h 2 μ ∧ Tendsto (fun m => eLpNorm (f m - h) 2 μ) atTop (𝓝 0) := by
  have hmeas : AEStronglyMeasurable h μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hf m).aestronglyMeasurable)
      (ae_of_all _ hlim)
  have hC' : Tendsto (fun p : ℕ × ℕ => eLpNorm (f p.1 - f p.2) 2 μ) (atTop ×ˢ atTop) (𝓝 0) := by
    have e : ∀ p : ℕ × ℕ, eLpNorm (f p.1 - f p.2) 2 μ =
        ENNReal.ofReal ((∫ x, ‖f p.1 x - f p.2 x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) := fun p =>
      eLpNorm_two_eq_ofReal_sqrt ((hf p.1).sub (hf p.2))
    simp_rw [e]
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := ((Real.continuousAt_rpow_const 0 (2 : ℝ)⁻¹ (Or.inr (by norm_num))).tendsto).comp hC
    simpa [Function.comp_def, Real.zero_rpow (by norm_num : (2 : ℝ)⁻¹ ≠ 0)] using this
  have hfat : ∀ m, eLpNorm (h - f m) 2 μ ≤ atTop.liminf (fun k => eLpNorm (f k - f m) 2 μ) := by
    intro m
    exact Lp.eLpNorm_lim_le_liminf_eLpNorm (fun k => ((hf k).sub (hf m)).aestronglyMeasurable)
      (h - f m) (hmeas.sub (hf m).aestronglyMeasurable) (ae_of_all _ fun x => (hlim x).sub_const (f m x))
  have hT : Tendsto (fun m => eLpNorm (f m - h) 2 μ) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hev := (ENNReal.tendsto_nhds_zero.1 hC') ε hε
    rw [prod_atTop_atTop_eq, eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    rw [eventually_atTop]
    refine ⟨max N.1 N.2, fun m hm => ?_⟩
    rw [eLpNorm_sub_comm]
    refine (hfat m).trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    rw [eventually_atTop]
    refine ⟨max N.1 N.2, fun k hk => hN (k, m) ?_⟩
    exact ⟨le_trans (le_max_left _ _) hk, le_trans (le_max_right _ _) hm⟩
  refine ⟨?_, hT⟩
  obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have hd : MemLp (f m - h) 2 μ := hm.trans ENNReal.one_lt_top
  have : h = f m - (f m - h) := by abel
  rw [this]
  exact (hf m).sub hd

/-- Continuity of `(u, v) ↦ ∫ u · conj v` along `L²`-convergent sequences. -/
theorem tendsto_integral_mul_conj {f f' : ℕ → α → ℂ} {h h' : α → ℂ}
    (hf : ∀ m, MemLp (f m) 2 μ) (hf' : ∀ m, MemLp (f' m) 2 μ) (hh : MemLp h 2 μ)
    (hh' : MemLp h' 2 μ)
    (hT : Tendsto (fun m => eLpNorm (f m - h) 2 μ) atTop (𝓝 0))
    (hT' : Tendsto (fun m => eLpNorm (f' m - h') 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, f m x * (starRingEnd ℂ) (f' m x) ∂μ) atTop
      (𝓝 (∫ x, h x * (starRingEnd ℂ) (h' x) ∂μ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf h hh).2 hT
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f' hf' h' hh').2 hT'
  have key : ∀ (u u' : α → ℂ) (hu : MemLp u 2 μ) (hu' : MemLp u' 2 μ),
      ∫ x, u x * (starRingEnd ℂ) (u' x) ∂μ =
        @inner ℂ _ _ (hu'.toLp u') (hu.toLp u) := by
    intro u u' hu hu'
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp, hu'.coeFn_toLp] with x hx hx'
    rw [hx, hx']
    simp
  have e : (fun m => ∫ x, f m x * (starRingEnd ℂ) (f' m x) ∂μ) =
      fun m => @inner ℂ _ _ ((hf' m).toLp (f' m)) ((hf m).toLp (f m)) := by
    funext m
    exact key _ _ (hf m) (hf' m)
  rw [e, key _ _ hh hh']
  exact h2.inner h1

/-- Continuity of `u ↦ ∫ ‖u‖²` along `L²`-convergent sequences. -/
theorem tendsto_integral_norm_sq {f : ℕ → α → ℂ} {h : α → ℂ}
    (hf : ∀ m, MemLp (f m) 2 μ) (hh : MemLp h 2 μ)
    (hT : Tendsto (fun m => eLpNorm (f m - h) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, ‖f m x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖h x‖ ^ 2 ∂μ)) := by
  have H := tendsto_integral_mul_conj hf hf hh hh hT hT
  have e : ∀ u : α → ℂ, ∫ x, u x * (starRingEnd ℂ) (u x) ∂μ = ((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro u
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e] at H
  have := (Complex.continuous_re.tendsto _).comp H
  simpa [Function.comp_def] using this

end L2

/-! ### Wave packets with coefficients vanishing outside a compact set -/

section Packet

variable {n : ℕ} {ι X : Type*} [Fintype ι]

/-- The wave packet `g ↦ ∫ ∑ j, c j x · Φ j x g dσ(x)` with coefficients `c j` and kernels
`Φ j x g` (in the application `Φ j x g = E j (i e(x)) g`). -/
def packet (σ : Measure (Fin n → ℝ)) (c : ι → (Fin n → ℝ) → ℂ)
    (Φ : ι → (Fin n → ℝ) → X → ℂ) (g : X) : ℂ :=
  ∫ x, ∑ j, c j x * Φ j x g ∂σ

/-- The Hermitian form `z ↦ ∑ j, ∑ j', z j · conj (z j') · Gm j j'` of a Gram matrix `Gm`. -/
def gramForm (Gm : ι → ι → ℂ) (z : ι → ℂ) : ℂ :=
  ∑ j, ∑ j', z j * (starRingEnd ℂ) (z j') * Gm j j'

theorem continuous_gramForm (Gm : ι → ι → ℂ) : Continuous (gramForm Gm) := by
  unfold gramForm
  fun_prop

theorem norm_gramForm_le (Gm : ι → ι → ℂ) {z : ι → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ j, ‖z j‖ ≤ R) : ‖gramForm Gm z‖ ≤ ∑ j, ∑ j', R * R * ‖Gm j j'‖ := by
  unfold gramForm
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j' _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have h1 := hz j
  have h2 := hz j'
  gcongr

theorem gramForm_zero (Gm : ι → ι → ℂ) : gramForm Gm 0 = 0 := by
  simp [gramForm]

variable {σ : Measure (Fin n → ℝ)} {N : Set (Fin n → ℝ)}

theorem aestronglyMeasurable_sum_mul (hN : MeasurableSet N) {c : ι → (Fin n → ℝ) → ℂ}
    (hc : ∀ j, AEStronglyMeasurable (c j) σ) (hcN : ∀ j x, x ∉ N → c j x = 0)
    {Ψ : ι → (Fin n → ℝ) → ℂ} (hΨ : ∀ j, ContinuousOn (Ψ j) N) :
    AEStronglyMeasurable (fun x => ∑ j, c j x * Ψ j x) σ := by
  refine aestronglyMeasurable_of_restrict_of_zero_off hN ?_ ?_
  · exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      (hc j).restrict.mul ((hΨ j).aestronglyMeasurable hN)
  · intro x hx
    simp [hcN _ x hx]

theorem norm_sum_mul_le {c : ι → (Fin n → ℝ) → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hcA : ∀ j x, ‖c j x‖ ≤ A) (hcN : ∀ j x, x ∉ N → c j x = 0)
    {Ψ : ι → (Fin n → ℝ) → ℂ} {Cb : ι → ℝ} (hCb : ∀ j, ∀ x ∈ N, ‖Ψ j x‖ ≤ Cb j) (x : Fin n → ℝ) :
    ‖∑ j, c j x * Ψ j x‖ ≤ ∑ j, A * max (Cb j) 0 := by
  by_cases hx : x ∈ N
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hcA j x) ((hCb j x hx).trans (le_max_left _ _)) (norm_nonneg _) hA
  · simp only [hcN _ x hx, zero_mul, Finset.sum_const_zero, norm_zero]
    exact Finset.sum_nonneg fun j _ => mul_nonneg hA (le_max_right _ _)

theorem integrable_sum_mul (hN : IsCompact N) (hσN : σ N < ⊤) {c : ι → (Fin n → ℝ) → ℂ}
    (hc : ∀ j, AEStronglyMeasurable (c j) σ) {A : ℝ} (hA : 0 ≤ A)
    (hcA : ∀ j x, ‖c j x‖ ≤ A) (hcN : ∀ j x, x ∉ N → c j x = 0)
    {Ψ : ι → (Fin n → ℝ) → ℂ} (hΨ : ∀ j, ContinuousOn (Ψ j) N) :
    Integrable (fun x => ∑ j, c j x * Ψ j x) σ := by
  have hb : ∀ j, ∃ C, ∀ x ∈ N, ‖Ψ j x‖ ≤ C := fun j => hN.exists_bound_of_continuousOn (hΨ j)
  choose Cb hCb using hb
  refine integrable_of_bdd_of_zero_off hN.isClosed.measurableSet hσN
    (aestronglyMeasurable_sum_mul hN.isClosed.measurableSet hc hcN hΨ)
    (norm_sum_mul_le hA hcA hcN hCb) ?_
  intro x hx
  simp [hcN _ x hx]

theorem packet_sub (hN : IsCompact N) (hσN : σ N < ⊤) {c c' : ι → (Fin n → ℝ) → ℂ}
    (hc : ∀ j, AEStronglyMeasurable (c j) σ) (hc' : ∀ j, AEStronglyMeasurable (c' j) σ)
    {A : ℝ} (hA : 0 ≤ A) (hcA : ∀ j x, ‖c j x‖ ≤ A) (hcA' : ∀ j x, ‖c' j x‖ ≤ A)
    (hcN : ∀ j x, x ∉ N → c j x = 0) (hcN' : ∀ j x, x ∉ N → c' j x = 0)
    {Φ : ι → (Fin n → ℝ) → X → ℂ} (hΦ : ∀ j g, ContinuousOn (fun x => Φ j x g) N) (g : X) :
    packet σ c Φ g - packet σ c' Φ g = packet σ (fun j x => c j x - c' j x) Φ g := by
  unfold packet
  rw [← integral_sub (integrable_sum_mul hN hσN hc hA hcA hcN fun j => hΦ j g)
    (integrable_sum_mul hN hσN hc' hA hcA' hcN' fun j => hΦ j g)]
  congr 1
  funext x
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => (sub_mul _ _ _).symm

variable {Y : Type*} [MeasurableSpace Y] {μY : Measure Y}

/-- The analytic core of Lapid's proof of Lemma 10: if smooth coefficients `cs m` vanishing
outside a compact set `N` are uniformly bounded and converge almost everywhere to `c`, and the
smooth packets satisfy the norm bound `‖Θ_d‖² ≤ B ∫ Re (gramForm Gm d)`, then `Θ_{cs m} → Θ_c`
in `L²`, `Θ_c` is square integrable and satisfies the same bound. -/
theorem packet_core (out : Y → X) (hN : IsCompact N) (hσN : σ N < ⊤)
    {Φ : ι → (Fin n → ℝ) → X → ℂ} (hΦ : ∀ j g, ContinuousOn (fun x => Φ j x g) N)
    {c : ι → (Fin n → ℝ) → ℂ} {A : ℝ} (hA : 0 ≤ A)
    {cs : ℕ → ι → (Fin n → ℝ) → ℂ} (hcs : ∀ m j, ContDiff ℝ ∞ (cs m j))
    (hcsA : ∀ m j x, ‖cs m j x‖ ≤ A) (hcsN : ∀ m j x, x ∉ N → cs m j x = 0)
    (hlim : ∀ᵐ x ∂σ, ∀ j, Tendsto (fun m => cs m j x) atTop (𝓝 (c j x)))
    (Gm : ι → ι → ℂ) (B : ℝ)
    (HB : ∀ d : ι → (Fin n → ℝ) → ℂ, (∀ j, ContDiff ℝ ∞ (d j)) →
      (∀ j x, x ∉ N → d j x = 0) →
      MemLp (fun y => packet σ d Φ (out y)) 2 μY ∧
        ∫ y, ‖packet σ d Φ (out y)‖ ^ 2 ∂μY ≤ B * ∫ x, (gramForm Gm fun j => d j x).re ∂σ) :
    MemLp (fun y => packet σ c Φ (out y)) 2 μY ∧
      Tendsto (fun m => eLpNorm ((fun y => packet σ (cs m) Φ (out y)) -
        fun y => packet σ c Φ (out y)) 2 μY) atTop (𝓝 0) ∧
      ∫ y, ‖packet σ c Φ (out y)‖ ^ 2 ∂μY ≤ B * ∫ x, (gramForm Gm fun j => c j x).re ∂σ := by
  classical
  have hNm : MeasurableSet N := hN.isClosed.measurableSet
  have hcsm : ∀ m j, AEStronglyMeasurable (cs m j) σ := fun m j =>
    (hcs m j).continuous.aestronglyMeasurable
  have hcsc : ∀ m j, Continuous (cs m j) := fun m j => (hcs m j).continuous
  -- pointwise convergence of the packets
  have hpt : ∀ g, Tendsto (fun m => packet σ (cs m) Φ g) atTop (𝓝 (packet σ c Φ g)) := by
    intro g
    have hb : ∀ j, ∃ C, ∀ x ∈ N, ‖Φ j x g‖ ≤ C := fun j =>
      hN.exists_bound_of_continuousOn (hΦ j g)
    choose Cb hCb using hb
    refine tendsto_integral_of_bdd_of_zero_off hNm hσN
      (fun m => aestronglyMeasurable_sum_mul hNm (hcsm m) (hcsN m) fun j => hΦ j g)
      (fun m => norm_sum_mul_le hA (hcsA m) (hcsN m) hCb) ?_ ?_
    · intro m x hx
      simp [hcsN m _ x hx]
    · filter_upwards [hlim] with x hx
      exact tendsto_finsetSum _ fun j _ => (hx j).mul_const _
  -- the Gram forms of the differences tend to zero
  have hgram : Tendsto (fun p : ℕ × ℕ => ∫ x, (gramForm Gm fun j => cs p.1 j x - cs p.2 j x).re ∂σ)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h := tendsto_integral_of_bdd_of_zero_off (l := atTop ×ˢ atTop) (F₀ := fun _ => (0 : ℝ))
      (F := fun (p : ℕ × ℕ) x => (gramForm Gm fun j => cs p.1 j x - cs p.2 j x).re)
      (B := ∑ j, ∑ j', (A + A) * (A + A) * ‖Gm j j'‖) hNm hσN ?_ ?_ ?_ ?_
    · simpa using h
    · intro p
      refine Continuous.aestronglyMeasurable ?_
      exact Complex.continuous_re.comp ((continuous_gramForm Gm).comp
        (continuous_pi fun j => (hcsc p.1 j).sub (hcsc p.2 j)))
    · intro p x
      refine (Complex.abs_re_le_norm _).trans (norm_gramForm_le Gm (by positivity) fun j => ?_)
      exact (norm_sub_le _ _).trans (add_le_add (hcsA _ j x) (hcsA _ j x))
    · intro p x hx
      simp [gramForm, hcsN _ _ x hx]
    · filter_upwards [hlim] with x hx
      have hz : Tendsto (fun p : ℕ × ℕ => fun j => cs p.1 j x - cs p.2 j x) (atTop ×ˢ atTop)
          (𝓝 0) := by
        refine tendsto_pi_nhds.2 fun j => ?_
        have := ((hx j).comp tendsto_fst).sub ((hx j).comp tendsto_snd)
        simpa using this
      have := ((Complex.continuous_re.comp (continuous_gramForm Gm)).tendsto 0).comp hz
      simpa [Function.comp_def, gramForm_zero] using this
  -- Cauchy property in `L²`
  have hdiff : ∀ m k y, packet σ (cs m) Φ (out y) - packet σ (cs k) Φ (out y) =
      packet σ (fun j x => cs m j x - cs k j x) Φ (out y) := fun m k y =>
    packet_sub hN hσN (hcsm m) (hcsm k) hA (hcsA m) (hcsA k) (hcsN m) (hcsN k) hΦ (out y)
  have hcau : Tendsto (fun p : ℕ × ℕ =>
      ∫ y, ‖packet σ (cs p.1) Φ (out y) - packet σ (cs p.2) Φ (out y)‖ ^ 2 ∂μY)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have hle : ∀ p : ℕ × ℕ,
        ∫ y, ‖packet σ (cs p.1) Φ (out y) - packet σ (cs p.2) Φ (out y)‖ ^ 2 ∂μY ≤
          B * ∫ x, (gramForm Gm fun j => cs p.1 j x - cs p.2 j x).re ∂σ := by
      intro p
      simp_rw [hdiff]
      exact (HB (fun j x => cs p.1 j x - cs p.2 j x) (fun j => (hcs _ j).sub (hcs _ j))
        (fun j x hx => by simp [hcsN _ j x hx])).2
    refine squeeze_zero (fun p => integral_nonneg fun y => by positivity) hle ?_
    simpa using hgram.const_mul B
  obtain ⟨hmem, hT⟩ := memLp_two_and_tendsto_of_cauchy
    (f := fun m y => packet σ (cs m) Φ (out y)) (h := fun y => packet σ c Φ (out y))
    (fun m => (HB (cs m) (hcs m) (hcsN m)).1) (fun y => hpt (out y)) hcau
  refine ⟨hmem, hT, ?_⟩
  -- the norm bound in the limit
  have h1 := tendsto_integral_norm_sq (fun m => (HB (cs m) (hcs m) (hcsN m)).1) hmem hT
  have h2 : Tendsto (fun m => B * ∫ x, (gramForm Gm fun j => cs m j x).re ∂σ) atTop
      (𝓝 (B * ∫ x, (gramForm Gm fun j => c j x).re ∂σ)) := by
    refine Tendsto.const_mul B ?_
    refine tendsto_integral_of_bdd_of_zero_off (B := ∑ j, ∑ j', A * A * ‖Gm j j'‖) hNm hσN ?_ ?_
      ?_ ?_
    · intro m
      exact (Complex.continuous_re.comp ((continuous_gramForm Gm).comp
        (continuous_pi fun j => hcsc m j))).aestronglyMeasurable
    · intro m x
      exact (Complex.abs_re_le_norm _).trans (norm_gramForm_le Gm hA fun j => hcsA m j x)
    · intro m x hx
      simp [gramForm, hcsN _ _ x hx]
    · filter_upwards [hlim] with x hx
      exact ((Complex.continuous_re.comp (continuous_gramForm Gm)).tendsto _).comp
        (tendsto_pi_nhds.2 hx)
  exact le_of_tendsto_of_tendsto' h1 h2 fun m => (HB (cs m) (hcs m) (hcsN m)).2

end Packet

end Langlands.Global.BoundedWavePacket
