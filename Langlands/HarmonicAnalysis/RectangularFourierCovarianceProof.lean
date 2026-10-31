import Langlands.HarmonicAnalysis.RectangularFourierCovarianceStatement
import Langlands.HarmonicAnalysis.SelfDualSigmaFiniteProof
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Mathlib.Topology.Metrizable.Uniformity

/-! Covariance of the chosen full rectangular Fourier equivalence under right
translation. Second countability of the field is derived from scalar self-duality,
so that the published determinant change of variables applies to the supplied
nested product measure. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Pointwise NNReal ENNReal Uniformity

namespace Langlands.HarmonicAnalysis

universe uK

section Topology

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [T2Space K]

/-- In a locally compact Hausdorff topological ring whose underlying ring is a field and
in which `0` is not isolated, `0` has a countable neighbourhood basis: the compact dilates
`u ^ n • V` of a compact neighbourhood `V` by a unit `u` of Haar character below one. -/
theorem nhds_zero_isCountablyGenerated_of_addHaar [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] [(𝓝[≠] (0 : K)).NeBot] :
    (𝓝 (0 : K)).IsCountablyGenerated := by
  obtain ⟨V, hVc, hV0⟩ := exists_compact_mem_nhds (0 : K)
  have hμV : μ V ≠ ∞ := hVc.measure_lt_top.ne
  have hμV0 : μ V ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hV0).ne'
  -- A nonzero interior point `p` of `V`, separated from `0` by disjoint open sets.
  obtain ⟨p, hp0, hpV⟩ :=
    Filter.nonempty_of_mem (inter_mem_nhdsWithin ({0}ᶜ : Set K) (interior_mem_nhds.2 hV0))
  obtain ⟨U, O, hU, hO, h0U, hpO, hUO⟩ := t2_separation (Ne.symm hp0)
  -- `V \ O` is a neighbourhood of `0` of strictly smaller measure than `V`.
  have hV' : V \ O ∈ 𝓝 (0 : K) :=
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
  have hev : ∀ᶠ b in 𝓝 (0 : K), ∀ v ∈ V, b * v ∈ V \ O :=
    hVc.eventually_forall_of_forall_eventually fun v _ => by
      have h : Tendsto (fun z : K × K => z.1 * z.2) (𝓝 (0, v)) (𝓝 (0 * v)) :=
        continuous_mul.tendsto (0, v)
      rw [zero_mul] at h
      exact h.eventually_mem hV'
  obtain ⟨b, ⟨hbmul, -⟩, hb0⟩ :=
    (((hev.and hV0).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ({0}ᶜ : Set K) ∈ 𝓝[≠] (0 : K))).exists
  set u : Kˣ := Units.mk0 b hb0 with hu_def
  have hΔ : ∀ (g : Kˣ) (s : Set K), (distribHaarChar K g : ℝ≥0∞) * μ s = μ (g • s) :=
    fun g s => distribHaarChar_mul μ g s
  have huV' : u • V ⊆ V \ O := by
    rintro _ ⟨v, hv, rfl⟩
    exact hbmul v hv
  have huV : u • V ⊆ V := huV'.trans sdiff_subset
  have hΔu : distribHaarChar K u < 1 := by
    by_contra h
    replace h := not_lt.1 h
    have h1 : μ V ≤ (distribHaarChar K u : ℝ≥0∞) * μ V := by
      calc μ V = 1 * μ V := (one_mul _).symm
        _ ≤ _ := by gcongr; exact_mod_cast h
    exact lt_irrefl _ (((h1.trans_eq (hΔ u V)).trans (measure_mono huV')).trans_lt hlt)
  -- The decreasing compact dilates `u ^ n • V`.
  let S : ℕ → Set K := fun n => (u ^ n) • V
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
    set w : Kˣ := Units.mk0 x hx0' with hw_def
    have hVV : μ (V * V) ≠ ∞ := (hVc.mul hVc).measure_lt_top.ne
    have hbound : ∀ n : ℕ, (distribHaarChar K w : ℝ≥0∞) * μ V ≤
        (distribHaarChar K u : ℝ≥0∞) ^ n * μ (V * V) := by
      intro n
      have hxn : (u ^ n)⁻¹ • x ∈ V := mem_smul_set_iff_inv_smul_mem.1 (hx n)
      have hsub : ((u ^ n)⁻¹ * w) • V ⊆ V * V := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨(u ^ n)⁻¹ • x, hxn, v, hv, ?_⟩
        simp [Units.smul_def, hw_def, mul_assoc]
      calc (distribHaarChar K w : ℝ≥0∞) * μ V = μ (w • V) := hΔ w V
        _ = μ ((u ^ n) • ((u ^ n)⁻¹ * w) • V) := by rw [smul_smul, mul_inv_cancel_left]
        _ = (distribHaarChar K (u ^ n) : ℝ≥0∞) * μ (((u ^ n)⁻¹ * w) • V) := (hΔ _ _).symm
        _ ≤ (distribHaarChar K (u ^ n) : ℝ≥0∞) * μ (V * V) := by gcongr
        _ = (distribHaarChar K u : ℝ≥0∞) ^ n * μ (V * V) := by rw [map_pow]; push_cast; rfl
    have hlim : Tendsto (fun n : ℕ => (distribHaarChar K u : ℝ≥0∞) ^ n * μ (V * V))
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const
        ((ENNReal.tendsto_pow_atTop_nhds_zero_iff
          (r := (distribHaarChar K u : ℝ≥0∞))).2 (by exact_mod_cast hΔu)) (Or.inr hVV)
      simpa using h
    have hle := ge_of_tendsto' hlim hbound
    have hne : (distribHaarChar K w : ℝ≥0∞) * μ V ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (distribHaarChar_pos (A := K) (g := w)).ne') hμV0
    exact hne (le_zero_iff.1 hle)
  -- Each dilate is a neighbourhood of `0`, and every neighbourhood contains one.
  have hS_nhds : ∀ n, S n ∈ 𝓝 (0 : K) := fun n => by
    have h := (smul_mem_nhds_smul_iff (u ^ n) (t := V) (a := (0 : K))).2 hV0
    rwa [smul_zero] at h
  have hbasis : (𝓝 (0 : K)).HasBasis (fun _ : ℕ => True) S := by
    refine ⟨fun t => ⟨fun ht => ?_, fun ⟨n, _, hn⟩ => mem_of_superset (hS_nhds n) hn⟩⟩
    have ht' : t ∈ 𝓝ˢ (⋂ n, S n) := by
      refine nhdsSet_mono hS_inter ?_
      rwa [nhdsSet_singleton]
    obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact hS_anti.directed_ge hS_cpt ht'
    exact ⟨n, trivial, hn⟩
  exact hbasis.isCountablyGenerated

end Topology

/-- A sigma-compact commutative topological additive group with a countable
neighbourhood basis at `0` is second countable: its right uniformity is countably
generated, hence pseudometrizable. -/
theorem secondCountableTopology_of_nhds_zero_isCountablyGenerated
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SigmaCompactSpace G] [(𝓝 (0 : G)).IsCountablyGenerated] : SecondCountableTopology G := by
  let := IsTopologicalAddGroup.rightUniformSpace G
  have := isUniformAddGroup_of_addCommGroup (G := G)
  have : (𝓤 G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric G
  exact EMetric.secondCountable_of_sigmaCompact G

section SelfDual

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]

/-- Scalar self-duality forces second countability of the field. If `0` is isolated the
self-dual Haar measure is finite, so the discrete field is compact and hence finite;
otherwise the field is sigma-compact with a countable neighbourhood basis at `0`. -/
theorem secondCountableTopology_of_isSelfDual {ψ : UnitaryAdditiveCharacter K}
    {μ : AdditiveHaarMeasure K} (hsd : IsSelfDual ψ μ) : SecondCountableTopology K := by
  by_cases h0 : IsOpen ({0} : Set K)
  · have := isFiniteMeasure_of_isSelfDual_of_isOpen_singleton_zero hsd h0
    have : DiscreteTopology K := discreteTopology_of_isOpen_singleton_zero h0
    have : CompactSpace K := by
      by_contra hK
      have : NoncompactSpace K := ⟨fun h => hK ⟨h⟩⟩
      exact measure_ne_top μ.measure univ (measure_univ_of_isAddLeftInvariant μ.measure)
    have : Finite K := finite_of_compact_of_discrete
    infer_instance
  · have : (𝓝[≠] (0 : K)).NeBot :=
      ⟨fun h => h0 ((isOpen_singleton_iff_punctured_nhds 0).2 h)⟩
    have := sigmaCompactSpace_of_addHaar μ.measure
    have := nhds_zero_isCountablyGenerated_of_addHaar μ.measure
    exact secondCountableTopology_of_nhds_zero_isCountablyGenerated

end SelfDual

section ChangeOfVariables

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]

/-- Multiplication by a field unit `a` pushes a regular additive Haar measure forward to
the reciprocal of the intrinsic scalar Haar character of `a` times itself. -/
theorem map_mul_left_eq_inv_distribHaarChar (ν : Measure K) [ν.IsAddHaarMeasure]
    [ν.Regular] (a : Kˣ) :
    ν.map (fun x => (a : K) * x) = (distribHaarChar K a)⁻¹ • ν := by
  ext t ht
  rw [Measure.map_apply (continuous_const_mul (a : K)).measurable ht]
  have hpre : (fun x => (a : K) * x) ⁻¹' t = a⁻¹ • t := by
    ext x
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def,
      smul_eq_mul]
  rw [hpre, ← distribHaarChar_mul, map_inv]
  rfl

/-- Right multiplication by `g` on actual `r × s` matrices pushes the supplied nested
product measure forward to the reciprocal of the `r`-th power of the intrinsic scalar
Haar character of `det g` times itself. -/
theorem rectangularMeasure_map_mul_right [SecondCountableTopology K]
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure] {r s : ℕ}
    (g : GeneralLinear s K) :
    (RankinSelberg.rectangularMeasure μ r s).map (fun m => m * g.val) =
      ((distribHaarChar K (GeneralLinear.determinant g)) ^ r)⁻¹ •
        RankinSelberg.rectangularMeasure μ r s := by
  classical
  let χ : K →*₀ ℝ≥0 :=
    { toFun := fun x => if hx : x = 0 then 0 else distribHaarChar K (Units.mk0 x hx)
      map_zero' := by simp
      map_one' := by
        have : Units.mk0 (1 : K) one_ne_zero = 1 := Units.ext rfl
        simp only [one_ne_zero, ↓reduceDIte, this, map_one]
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        have hxy : x * y ≠ 0 := mul_ne_zero hx hy
        have hu : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := Units.ext rfl
        simp only [hx, hy, hxy, ↓reduceDIte, hu, map_mul] }
  have hχu (a : Kˣ) : χ a = distribHaarChar K a := by
    change (if hx : (a : K) = 0 then 0 else distribHaarChar K (Units.mk0 (a : K) hx)) = _
    simp only [a.ne_zero, ↓reduceDIte, Units.mk0_val]
  have hχ (a : K) (ha : a ≠ 0) :
      μ.measure.map (fun x => a * x) = (χ a)⁻¹ • μ.measure := by
    have h := map_mul_left_eq_inv_distribHaarChar μ.measure (Units.mk0 a ha)
    rw [← hχu] at h
    exact h
  have h := haarMeasure_map_rectangular μ.measure χ hχ
    (RankinSelberg.rectangularMeasure μ r s) (1 : Matrix (Fin r) (Fin r) K) g.val
    (by simp) (GeneralLinear.determinant g).ne_zero
  have hdet : χ (Matrix.det g.val) = distribHaarChar K (GeneralLinear.determinant g) :=
    hχu (GeneralLinear.determinant g)
  simp only [Matrix.one_mul, Matrix.det_one, map_one, one_pow, one_mul,
    Fintype.card_fin, hdet] at h
  exact h

end ChangeOfVariables

/-- Full rectangular Fourier covariance: the chosen full Fourier equivalence carries
right translation by `g` to the reciprocal of the `r`-th power of the intrinsic scalar
Haar character of `det g` times right translation by the inverse transpose of `g`. -/
theorem rectangularFourierCovariance : RectangularFourierCovarianceStatement.{uK} := by
  intro K _ _ _ _ _ _ _ _ ψ μ r s hsd g Φ
  have : SigmaFinite μ.measure := selfDualSigmaFinite K ψ μ hsd
  have : SecondCountableTopology K := secondCountableTopology_of_isSelfDual hsd
  have hmap : (RankinSelberg.rectangularMeasure μ r s).map
      (rectangularLeftRightHomeomorph (1 : GeneralLinear r K) g) =
      ((distribHaarChar K (GeneralLinear.determinant g)) ^ r)⁻¹ •
        RankinSelberg.rectangularMeasure μ r s := by
    have h1 : (⇑(rectangularLeftRightHomeomorph (1 : GeneralLinear r K) g)) =
        fun m => m * g.val := by
      funext m
      simp
    rw [h1]
    exact rectangularMeasure_map_mul_right μ g
  apply Hecke.TestFunction.ext
  intro b
  have h := rectangularFourierIntegral_leftRight ψ μ 1 g _ hmap Φ b
  simp only [Units.val_one, Matrix.one_mul, map_one] at h
  rw [rectangularFourierEquiv_apply]
  change _ = ((((distribHaarChar K (GeneralLinear.determinant g) : ℝ) : ℂ) ^ r)⁻¹) *
    rectangularFourierEquiv ψ μ r s hsd Φ (b * (GeneralLinear.inverseTranspose s K g).val)
  rw [rectangularFourierEquiv_apply]
  refine h.trans ?_
  push_cast
  rfl

end Langlands.HarmonicAnalysis
