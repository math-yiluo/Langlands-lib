import Langlands.HarmonicAnalysis.SelfDualSigmaFiniteStatement
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.SpecificLimits.Basic

/-! Sigma-finiteness of self-dual additive Haar measures: sigma-compactness in the
nondiscrete case, and finiteness of the measure in the discrete case. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Pointwise NNReal ENNReal

namespace Langlands.HarmonicAnalysis

universe u

section SigmaCompact

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [LocallyCompactSpace F] [T2Space F]

/-- A locally compact Hausdorff topological ring whose underlying ring is a field and in which
`0` is not isolated is sigma-compact. The proof uses a regular additive Haar measure only to
compare dilates; continuity of inversion is not assumed. -/
theorem sigmaCompactSpace_of_addHaar [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] [(𝓝[≠] (0 : F)).NeBot] :
    SigmaCompactSpace F := by
  obtain ⟨V, hVc, hV0⟩ := exists_compact_mem_nhds (0 : F)
  have hμV : μ V ≠ ∞ := hVc.measure_lt_top.ne
  have hμV0 : μ V ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hV0).ne'
  -- A nonzero interior point `p` of `V`, separated from `0` by disjoint open sets.
  obtain ⟨p, hp0, hpV⟩ :=
    Filter.nonempty_of_mem (inter_mem_nhdsWithin ({0}ᶜ : Set F) (interior_mem_nhds.2 hV0))
  obtain ⟨U, O, hU, hO, h0U, hpO, hUO⟩ := t2_separation (Ne.symm hp0)
  -- `V \ O` is a neighbourhood of `0` of strictly smaller measure than `V`.
  have hV' : V \ O ∈ 𝓝 (0 : F) :=
    Filter.mem_of_superset (inter_mem hV0 (hU.mem_nhds h0U))
      fun x hx => ⟨hx.1, fun hxO => Set.disjoint_left.1 hUO hx.2 hxO⟩
  have hlt : μ (V \ O) < μ V := by
    have hpos : μ (V ∩ O) ≠ 0 := by
      refine (lt_of_lt_of_le ((isOpen_interior.inter hO).measure_pos μ ⟨p, hpV, hpO⟩) ?_).ne'
      exact measure_mono (inter_subset_inter_left _ interior_subset)
    have hfin : μ (V \ O) ≠ ∞ := ne_top_of_le_ne_top hμV (measure_mono sdiff_subset)
    calc μ (V \ O) < μ (V \ O) + μ (V ∩ O) := ENNReal.lt_add_right hfin hpos
      _ = μ V := by rw [add_comm, measure_inter_add_sdiff _ hO.measurableSet]
  -- A nonzero `b ∈ V` with `b • V ⊆ V \ O`, by the tube lemma.
  have hev : ∀ᶠ b in 𝓝 (0 : F), ∀ v ∈ V, b * v ∈ V \ O :=
    hVc.eventually_forall_of_forall_eventually fun v _ => by
      have h : Tendsto (fun z : F × F => z.1 * z.2) (𝓝 (0, v)) (𝓝 (0 * v)) :=
        continuous_mul.tendsto (0, v)
      rw [zero_mul] at h
      exact h.eventually_mem hV'
  obtain ⟨b, ⟨hbmul, hbV⟩, hb0⟩ :=
    (((hev.and hV0).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ({0}ᶜ : Set F) ∈ 𝓝[≠] (0 : F))).exists
  set u : Fˣ := Units.mk0 b hb0 with hu_def
  have hΔ : ∀ (g : Fˣ) (s : Set F), (distribHaarChar F g : ℝ≥0∞) * μ s = μ (g • s) :=
    fun g s => distribHaarChar_mul μ g s
  have huV' : u • V ⊆ V \ O := by
    rintro _ ⟨v, hv, rfl⟩
    exact hbmul v hv
  have huV : u • V ⊆ V := huV'.trans sdiff_subset
  have hΔu : distribHaarChar F u < 1 := by
    by_contra h
    replace h := not_lt.1 h
    have h1 : μ V ≤ (distribHaarChar F u : ℝ≥0∞) * μ V := by
      calc μ V = 1 * μ V := (one_mul _).symm
        _ ≤ _ := by gcongr; exact_mod_cast h
    exact lt_irrefl _ (((h1.trans_eq (hΔ u V)).trans (measure_mono huV')).trans_lt hlt)
  -- The decreasing compact dilates `u ^ n • V`.
  let S : ℕ → Set F := fun n => (u ^ n) • V
  have hS_anti : Antitone S := antitone_nat_of_succ_le fun n => by
    change (u ^ (n + 1)) • V ⊆ (u ^ n) • V
    rw [pow_succ, mul_smul]
    exact smul_set_mono huV
  have hS_cpt : ∀ n, IsCompact (S n) := fun n => hVc.smul _
  -- Their intersection is `{0}`: a nonzero point would force unbounded measure inside `V * V`.
  have hS_inter : (⋂ n, S n) ⊆ {0} := by
    intro x hx
    rw [mem_iInter] at hx
    by_contra hx0
    have hx0' : x ≠ 0 := hx0
    set w : Fˣ := Units.mk0 x hx0' with hw_def
    have hVV : μ (V * V) ≠ ∞ := (hVc.mul hVc).measure_lt_top.ne
    have hbound : ∀ n : ℕ, (distribHaarChar F w : ℝ≥0∞) * μ V ≤
        (distribHaarChar F u : ℝ≥0∞) ^ n * μ (V * V) := by
      intro n
      have hxn : (u ^ n)⁻¹ • x ∈ V := mem_smul_set_iff_inv_smul_mem.1 (hx n)
      have hsub : ((u ^ n)⁻¹ * w) • V ⊆ V * V := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨(u ^ n)⁻¹ • x, hxn, v, hv, ?_⟩
        simp [Units.smul_def, hw_def, mul_assoc]
      calc (distribHaarChar F w : ℝ≥0∞) * μ V = μ (w • V) := hΔ w V
        _ = μ ((u ^ n) • ((u ^ n)⁻¹ * w) • V) := by rw [smul_smul, mul_inv_cancel_left]
        _ = (distribHaarChar F (u ^ n) : ℝ≥0∞) * μ (((u ^ n)⁻¹ * w) • V) := (hΔ _ _).symm
        _ ≤ (distribHaarChar F (u ^ n) : ℝ≥0∞) * μ (V * V) := by gcongr
        _ = (distribHaarChar F u : ℝ≥0∞) ^ n * μ (V * V) := by rw [map_pow]; push_cast; rfl
    have hlim : Tendsto (fun n : ℕ => (distribHaarChar F u : ℝ≥0∞) ^ n * μ (V * V))
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const
        ((ENNReal.tendsto_pow_atTop_nhds_zero_iff
          (r := (distribHaarChar F u : ℝ≥0∞))).2 (by exact_mod_cast hΔu)) (Or.inr hVV)
      simpa using h
    have hle := ge_of_tendsto' hlim hbound
    have hne : (distribHaarChar F w : ℝ≥0∞) * μ V ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (distribHaarChar_pos (A := F) (g := w)).ne') hμV0
    exact hne (le_zero_iff.1 hle)
  -- Every point lands in `V` after multiplication by a power of `b`.
  refine ⟨⟨fun n => (u ^ n)⁻¹ • V, fun n => hVc.smul _, eq_univ_of_forall fun x => ?_⟩⟩
  have hW : (fun y => x * y) ⁻¹' V ∈ 𝓝ˢ (⋂ n, S n) := by
    refine nhdsSet_mono hS_inter ?_
    rw [nhdsSet_singleton]
    have h : Tendsto (fun y => x * y) (𝓝 0) (𝓝 (x * 0)) := (continuous_const_mul x).tendsto 0
    rw [mul_zero] at h
    exact h hV0
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact hS_anti.directed_ge hS_cpt hW
  refine mem_iUnion.2 ⟨n + 1, ?_⟩
  rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
  have h2 : x * ((u ^ n) • b) ∈ V := hn (smul_mem_smul_set hbV)
  convert h2 using 1
  have hub : (u : F) = b := rfl
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, hub]
  ring

/-- A locally compact Hausdorff topological ring whose underlying ring is a field and in which
`0` is not isolated is sigma-compact (measure-free form of `sigmaCompactSpace_of_addHaar`). -/
theorem sigmaCompactSpace_of_nhdsNE_neBot [(𝓝[≠] (0 : F)).NeBot] : SigmaCompactSpace F := by
  borelize F
  exact sigmaCompactSpace_of_addHaar (Measure.addHaarMeasure (Classical.arbitrary _))

end SigmaCompact

section Discrete

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F]

/-- If `0` is isolated, self-duality forces the Haar measure to be finite: the Fourier transform
of the indicator of `{0}` is the nonzero constant `μ {0}`, whose integrability is required by
the second-integral clause of `IsSelfDual`. -/
theorem isFiniteMeasure_of_isSelfDual_of_isOpen_singleton_zero
    {ψ : UnitaryAdditiveCharacter F} {μ : AdditiveHaarMeasure F} (hself : IsSelfDual ψ μ)
    (h0 : IsOpen ({0} : Set F)) : IsFiniteMeasure μ.measure := by
  have : DiscreteTopology F := discreteTopology_of_isOpen_singleton_zero h0
  let f : SchwartzBruhat F :=
    ⟨Set.indicator {0} 1, IsLocallyConstant.of_discrete _,
      HasCompactSupport.intro isCompact_singleton fun x hx => Set.indicator_of_notMem hx _⟩
  have hc0 : μ.measure {0} ≠ 0 := (h0.measure_pos μ.measure ⟨0, rfl⟩).ne'
  have hctop : μ.measure {0} ≠ ∞ := isCompact_singleton.measure_lt_top.ne
  have hF : ∀ y, fourierTransform ψ μ f y = (μ.measure.real {0} : ℂ) := by
    intro y
    change ∫ x, ψ.complex (x * y) * f x ∂μ.measure = _
    have h : (fun x => ψ.complex (x * y) * f x) = Set.indicator {0} (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x = 0
      · subst hx
        simp [f]
      · simp [f, hx]
    rw [h, integral_indicator_const _ (measurableSet_singleton 0)]
    simp
  have hint := (hself f).1 0
  have h : (fun x => ψ.complex (x * 0) * fourierTransform ψ μ f x) =
      fun _ => (μ.measure.real {0} : ℂ) := by
    funext x
    simp [hF]
  rw [h] at hint
  refine (integrable_const_iff_isFiniteMeasure ?_).1 hint
  exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hc0 hctop).ne'

end Discrete

/-- Every additive Haar measure that is self-dual for some unitary additive character is
sigma-finite. -/
theorem selfDualSigmaFinite : SelfDualSigmaFiniteStatement.{u} := by
  intro F _ _ _ _ _ _ _ _ ψ μ hself
  by_cases h0 : IsOpen ({0} : Set F)
  · have := isFiniteMeasure_of_isSelfDual_of_isOpen_singleton_zero hself h0
    infer_instance
  · have : (𝓝[≠] (0 : F)).NeBot := ⟨fun h => h0 ((isOpen_singleton_iff_punctured_nhds 0).2 h)⟩
    have := sigmaCompactSpace_of_addHaar μ.measure
    infer_instance

end Langlands.HarmonicAnalysis
