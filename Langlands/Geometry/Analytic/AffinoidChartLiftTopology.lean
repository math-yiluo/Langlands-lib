import Langlands.Geometry.Analytic.AffinoidChartLiftTopologyStatement
import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover

/-! # Topology of chart systems over an affinoid atlas -/

noncomputable section

universe u v w u' w'

namespace Langlands.Analytic

open Set Topology Filter
open scoped Topology

namespace AtlasTopology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {τ : Set (Set X)} {f : Y → X}

/-- Pullback of the finite neighborhood witnesses of a quasinet. Empty
inverse images are retained. -/
theorem IsQuasinet.preimage_image (hτ : IsQuasinet τ) (hf : Continuous f) :
    IsQuasinet ((Set.preimage f) '' τ) := by
  intro y
  obtain ⟨σ, hσ, hστ, hσy, hσn⟩ := hτ (f y)
  refine ⟨(Set.preimage f) '' σ, hσ.image _, image_mono hστ, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact hσy V hV
  · apply mem_of_superset (hf.continuousAt.preimage_mem_nhds hσn)
    rintro z ⟨V, hV, hzV⟩
    exact ⟨_, ⟨V, hV, rfl⟩, hzV⟩

/-- The overlap refinements of a net pull back along any continuous map. -/
theorem IsNet.preimage_image (hτ : IsNet τ) (hf : Continuous f) :
    IsNet ((Set.preimage f) '' τ) := by
  refine ⟨hτ.1.preimage_image hf, ?_⟩
  rintro _ ⟨U, hU, rfl⟩ _ ⟨V, hV, rfl⟩
  apply (isQuasinet_restrictedFamily_iff _ _).2
  intro S hS z hz
  rcases mem_singleton_iff.1 hS with rfl
  obtain ⟨σ, hσ, hστ, hσsub, hσn⟩ :=
    (isQuasinet_restrictedFamily_iff τ (U ∩ V)).1 (hτ.2 U hU V hV)
      (U ∩ V) (mem_singleton _) (f z) hz
  refine ⟨(Set.preimage f) '' σ, hσ.image _, image_mono hστ, ?_, ?_⟩
  · rintro _ ⟨W, hW, rfl⟩
    exact ⟨fun y hy => (hσsub W hW).1 hy, (hσsub W hW).2⟩
  · have hn : f ⁻¹' ⋃₀ σ ∈ 𝓝[f ⁻¹' U ∩ f ⁻¹' V] z :=
      hf.continuousWithinAt.tendsto_nhdsWithin (fun _ h => h) hσn
    apply mem_of_superset hn
    rintro y ⟨W, hW, hyW⟩
    exact ⟨_, ⟨W, hW, rfl⟩, hyW⟩

end AtlasTopology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Compact subsets of an overlap have finite covers by common charts, even
when the ambient analytic space is not Hausdorff. -/
theorem exists_finite_charts_cover_compact_inter (i j : a.Index) {S : Set X}
    (hS : IsCompact S) (hsub : S ⊆ range (a.chart i) ∩ range (a.chart j)) :
    ∃ T : Set a.Index, T.Finite ∧
      (∀ m ∈ T, range (a.chart m) ⊆ range (a.chart i) ∩ range (a.chart j)) ∧
      S ⊆ ⋃ m ∈ T, range (a.chart m) := by
  obtain ⟨σ, hf, hs, hσ, hcov⟩ :=
    a.isNet_chartFamily.exists_finite_cover_of_subset_inter
      ⟨i, rfl⟩ ⟨j, rfl⟩ hS hsub
  refine ⟨(fun m => range (a.chart m)) ⁻¹' σ,
    hf.preimage a.chartDomain_injective.injOn, fun m hm => hσ _ hm, ?_⟩
  intro x hx
  obtain ⟨V, hV, hxV⟩ := hcov hx
  obtain ⟨m, rfl⟩ := hs hV
  exact mem_iUnion₂.2 ⟨m, hV, hxV⟩

end IndexedAffinoidAtlas

namespace AffinoidChartSystem

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type u'} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  {X : Type v} [TopologicalSpace X]

namespace AtlasProjection

variable {C : AffinoidChartSystem.{u', w'} L}
  {a : IndexedAffinoidAtlas.{u, v, w} K X} (P : C.AtlasProjection a)

/-- Two compact sets contained in a Hausdorff subspace have compact
intersection in the original ambient topology. -/
theorem isCompact_inter_in_t2 {U S T : Set X} [T2Space U]
    (hS : IsCompact S) (hT : IsCompact T) (hSU : S ⊆ U) (hTU : T ⊆ U) :
    IsCompact (S ∩ T) := by
  have hS' : IsCompact (Subtype.val ⁻¹' S : Set U) :=
    IsInducing.subtypeVal.isCompact_preimage' hS (by simpa using hSU)
  have hT' : IsCompact (Subtype.val ⁻¹' T : Set U) :=
    IsInducing.subtypeVal.isCompact_preimage' hT (by simpa using hTU)
  have h := (hS'.inter hT').image continuous_subtype_val
  convert h using 1
  ext x
  constructor
  · rintro ⟨hxS, hxT⟩
    exact ⟨⟨x, hSU hxS⟩, ⟨hxS, hxT⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

/-- A compact cutoff in each of two charts reduces their gluing relation to
finitely many common affinoid domains. -/
theorem isClosed_chart_preimage_image_inter (i j : a.Index)
    {U : Set X} [T2Space U]
    {F : Set (BanachSpectrum (C.algebra (P.chartIndex i)))}
    {D : Set (BanachSpectrum (a.algebra j))}
    (hF : IsCompact F) (hD : IsCompact D)
    (hFU : (a.chart i ∘ P.chartPoint i) '' F ⊆ U) (hDU : a.chart j '' D ⊆ U) :
    IsClosed (C.chart (P.chartIndex j) ⁻¹' (C.chart (P.chartIndex i) '' F) ∩
      P.chartPoint j ⁻¹' D) := by
  classical
  let S := (a.chart i ∘ P.chartPoint i) '' F ∩ a.chart j '' D
  have hS : IsCompact S := isCompact_inter_in_t2
    (hF.image ((a.isEmbedding_chart i).continuous.comp (P.chartPoint i).continuous))
    (hD.image (a.isEmbedding_chart j).continuous) hFU hDU
  obtain ⟨T, hT, hsub, hcov⟩ := a.exists_finite_charts_cover_compact_inter i j hS (by
    rintro x ⟨⟨s, hs, rfl⟩, t, ht, heq⟩
    exact ⟨⟨_, rfl⟩, ⟨t, heq⟩⟩)
  let hi (m : T) := P.sub_of_subset m.1 i ((hsub m.1 m.2).trans inter_subset_left)
  let hj (m : T) := P.sub_of_subset m.1 j ((hsub m.1 m.2).trans inter_subset_right)
  let E (m : T) : Set (BanachSpectrum (C.algebra (P.chartIndex m.1))) :=
    C.pull (hi m) ⁻¹' F ∩ (P.chartPoint j ∘ C.pull (hj m)) ⁻¹' D
  have heq : C.chart (P.chartIndex j) ⁻¹' (C.chart (P.chartIndex i) '' F) ∩
      P.chartPoint j ⁻¹' D = ⋃ m : T, C.pull (hj m) '' E m := by
    ext t
    constructor
    · rintro ⟨⟨s, hs, hst⟩, ht⟩
      have hx : a.chart j (P.chartPoint j t) ∈ S := by
        refine ⟨⟨s, hs, ?_⟩, ⟨_, ht, rfl⟩⟩
        change a.chart i (P.chartPoint i s) = a.chart j (P.chartPoint j t)
        rw [← P.pointMap_chart, ← P.pointMap_chart, hst]
      obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.1 (hcov hx)
      have htm : C.chart (P.chartIndex j) t ∈ range (C.chart (P.chartIndex m)) := by
        rw [P.range_chart]
        change P.pointMap (C.chart (P.chartIndex j) t) ∈ range (a.chart m)
        rw [P.pointMap_chart]
        exact hxm
      obtain ⟨z, hz⟩ := htm
      have hzj : C.pull (hj ⟨m, hm⟩) z = t :=
        C.chart_injective _ ((C.chart_pull _ z).trans hz)
      have hzi : C.pull (hi ⟨m, hm⟩) z = s :=
        C.chart_injective _ ((C.chart_pull _ z).trans (hz.trans hst.symm))
      refine mem_iUnion.2 ⟨⟨m, hm⟩, z, ⟨?_, ?_⟩, hzj⟩
      · change C.pull (hi ⟨m, hm⟩) z ∈ F
        rwa [hzi]
      · change P.chartPoint j (C.pull (hj ⟨m, hm⟩) z) ∈ D
        rwa [hzj]
    · intro ht
      obtain ⟨m, z, hz, rfl⟩ := mem_iUnion.1 ht
      exact ⟨⟨C.pull (hi m) z, hz.1,
        (C.chart_pull _ z).trans (C.chart_pull _ z).symm⟩, hz.2⟩
  rw [heq]
  have : Finite T := hT.to_subtype
  apply isClosed_iUnion_of_finite
  intro m
  apply IsCompact.isClosed
  apply IsCompact.image _ (C.continuous_pull _)
  exact ((hF.isClosed.preimage (C.continuous_pull _)).inter
    (hD.isClosed.preimage ((P.chartPoint j).continuous.comp (C.continuous_pull _)))).isCompact

/-- Compact chart pieces whose base images lie in an open Hausdorff subspace
have closed images over that subspace. -/
theorem isClosed_chart_image_over_open (i : a.Index) {U : Set X} (hU : IsOpen U)
    [T2Space U] {F : Set (BanachSpectrum (C.algebra (P.chartIndex i)))}
    (hF : IsCompact F) (hFU : (a.chart i ∘ P.chartPoint i) '' F ⊆ U) :
    IsClosed (Subtype.val ⁻¹' (C.chart (P.chartIndex i) '' F) :
      Set (P.pointMap ⁻¹' U)) := by
  have hopen : IsOpen (P.pointMap ⁻¹' U \ C.chart (P.chartIndex i) '' F) := by
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage, isOpen_sigma_iff]
    intro k
    obtain ⟨j, rfl⟩ := P.chartIndex.surjective k
    apply isOpen_iff_mem_nhds.2
    intro t ht
    change P.pointMap (C.chart (P.chartIndex j) t) ∈ U ∧
      C.chart (P.chartIndex j) t ∉ C.chart (P.chartIndex i) '' F at ht
    have htU : a.chart j (P.chartPoint j t) ∈ U := by
      simpa only [P.pointMap_chart] using ht.1
    obtain ⟨D, hDn, hDU, hD⟩ := local_compact_nhds
      ((a.isEmbedding_chart j).continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds htU))
    have hclosed := P.isClosed_chart_preimage_image_inter i j hF hD hFU
      (show a.chart j '' D ⊆ U from fun _ ⟨s, hs, h⟩ => h ▸ hDU hs)
    have hnot : t ∉ C.chart (P.chartIndex j) ⁻¹' (C.chart (P.chartIndex i) '' F) ∩
        P.chartPoint j ⁻¹' D := fun h => ht.2 h.1
    filter_upwards [hclosed.isOpen_compl.mem_nhds hnot,
      (P.chartPoint j).continuous.continuousAt.preimage_mem_nhds hDn] with s hs hsD
    change P.pointMap (C.chart (P.chartIndex j) s) ∈ U ∧
      C.chart (P.chartIndex j) s ∉ C.chart (P.chartIndex i) '' F
    rw [P.pointMap_chart]
    exact ⟨hDU hsD, fun h => hs ⟨h, hsD⟩⟩
  apply isOpen_compl_iff.1
  convert hopen.preimage continuous_subtype_val using 1
  ext z
  exact (and_iff_right z.2).symm

/-- Every chart is an embedding; only local Hausdorffness of the base is
needed. -/
theorem isEmbedding_chart (i : a.Index) : IsEmbedding (C.chart (P.chartIndex i)) := by
  suffices hclosed : ∀ F, IsClosed F →
      IsClosed (Subtype.val ⁻¹' (C.chart (P.chartIndex i) '' F) :
        Set (range (C.chart (P.chartIndex i)))) by
    have he : IsClosedEmbedding (Set.rangeFactorization (C.chart (P.chartIndex i))) := by
      apply IsClosedEmbedding.of_continuous_injective_isClosedMap
        ((C.continuous_chart _).subtype_mk _) (fun s t h => C.chart_injective _ (congrArg Subtype.val h))
      intro F hF
      convert hclosed F hF using 1
      ext z
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, hz⟩
        exact ⟨s, hs, Subtype.ext hz⟩
    exact IsEmbedding.subtypeVal.comp he.isEmbedding
  intro F hF
  apply isOpen_compl_iff.1
  apply isOpen_iff_mem_nhds.2
  intro z hz
  rcases z with ⟨z, hzchart⟩
  obtain ⟨s, rfl⟩ := hzchart
  change C.chart (P.chartIndex i) s ∉ C.chart (P.chartIndex i) '' F at hz
  have hsF : s ∉ F := fun h => hz ⟨s, h, rfl⟩
  obtain ⟨U₀, hU₀, hT₀⟩ := a.locallyHausdorff (a.chart i (P.chartPoint i s))
  let := hT₀
  let U := interior U₀
  have hUT : T2Space U :=
    T2Space.of_injective_continuous (Set.inclusion_injective interior_subset)
      (continuous_inclusion interior_subset)
  let := hUT
  have hsU : a.chart i (P.chartPoint i s) ∈ U := mem_interior_iff_mem_nhds.2 hU₀
  obtain ⟨D, hDn, hDU, hD⟩ := local_compact_nhds
    ((a.isEmbedding_chart i).continuous.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds hsU))
  let E := F ∩ P.chartPoint i ⁻¹' D
  have hE : IsCompact E :=
    (hF.inter (hD.isClosed.preimage (P.chartPoint i).continuous)).isCompact
  have hEU : (a.chart i ∘ P.chartPoint i) '' E ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hDU ht.2
  have hc := P.isClosed_chart_image_over_open i isOpen_interior hE hEU
  rw [(a.isEmbedding_chart i).isInducing.nhds_eq_comap] at hDn
  obtain ⟨W, hW, hWD⟩ := mem_comap.1 hDn
  have hsPU : P.pointMap (C.chart (P.chartIndex i) s) ∈ U := by
    rwa [P.pointMap_chart]
  have hnU : P.pointMap ⁻¹' U ∈ 𝓝 (C.chart (P.chartIndex i) s) :=
    P.pointMap.continuous.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hsPU)
  have hnW : P.pointMap ⁻¹' W ∈ 𝓝 (C.chart (P.chartIndex i) s) :=
    P.pointMap.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [P.pointMap_chart] using hW)
  have hsE : C.chart (P.chartIndex i) s ∉ C.chart (P.chartIndex i) '' E := by
    rintro ⟨t, ht, heq⟩
    exact hsF ((C.chart_injective _ heq) ▸ ht.1)
  have hlocal : (C.chart (P.chartIndex i) '' E)ᶜ ∈
      𝓝[P.pointMap ⁻¹' U] (C.chart (P.chartIndex i) s) := by
    rw [← map_nhds_subtype_val (⟨_, hsPU⟩ : P.pointMap ⁻¹' U)]
    exact hc.isOpen_compl.mem_nhds hsE
  have hnE : (C.chart (P.chartIndex i) '' E)ᶜ ∈ 𝓝 (C.chart (P.chartIndex i) s) :=
    (nhdsWithin_eq_nhds.mpr hnU) ▸ hlocal
  change Subtype.val ⁻¹' (C.chart (P.chartIndex i) '' F)ᶜ ∈ 𝓝 _
  filter_upwards [(continuous_subtype_val.continuousAt.preimage_mem_nhds hnW),
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hnE)] with y hyW hyE
  rintro ⟨t, ht, hty⟩
  apply hyE
  refine ⟨t, ⟨ht, ?_⟩, hty⟩
  apply hWD
  change a.chart i (P.chartPoint i t) ∈ W
  rw [← P.pointMap_chart, hty]
  exact hyW

include P in
/-- Finite compact cutoffs of a quasinet neighborhood lift to a Hausdorff
neighborhood in the quotient. -/
theorem locallyHausdorff (z : C.Space) :
    ∃ V : Set C.Space, V ∈ 𝓝 z ∧ T2Space V := by
  classical
  let x := P.pointMap z
  obtain ⟨U₀, hU₀, hT₀⟩ := a.locallyHausdorff x
  let := hT₀
  let U := interior U₀
  have hUT : T2Space U :=
    T2Space.of_injective_continuous (Set.inclusion_injective interior_subset)
      (continuous_inclusion interior_subset)
  let := hUT
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.2 hU₀
  obtain ⟨σ, hσ, hστ, hσx, hσn⟩ := a.isNet_chartFamily.1 x
  let S := (fun i => range (a.chart i)) ⁻¹' σ
  have hS : S.Finite := hσ.preimage a.chartDomain_injective.injOn
  have : Finite S := hS.to_subtype
  have H : ∀ i : S, ∃ (D : Set (BanachSpectrum (a.algebra i.1))) (W : Set X),
      IsCompact D ∧ a.chart i.1 '' D ⊆ U ∧ W ∈ 𝓝 x ∧ a.chart i.1 ⁻¹' W ⊆ D := by
    intro i
    obtain ⟨s, hs⟩ := hσx (range (a.chart i.1)) i.2
    have hsU : a.chart i.1 s ∈ U := hs ▸ hxU
    obtain ⟨D, hDn, hDU, hDc⟩ := local_compact_nhds
      ((a.isEmbedding_chart i.1).continuous.continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hsU))
    rw [(a.isEmbedding_chart i.1).isInducing.nhds_eq_comap] at hDn
    obtain ⟨W, hW, hWD⟩ := mem_comap.1 hDn
    refine ⟨D, W, hDc, ?_, ?_, hWD⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact hDU hs
    · simpa only [hs] using hW
  choose D W hDc hDU hWn hWD using H
  let V := U ∩ ⋃₀ σ ∩ ⋂ i : S, W i
  have hVU : V ⊆ U := fun _ h => h.1.1
  have hVn : V ∈ 𝓝 x :=
    inter_mem (inter_mem (isOpen_interior.mem_nhds hxU) hσn) (iInter_mem.2 hWn)
  refine ⟨P.pointMap ⁻¹' V, P.pointMap.continuous.continuousAt.preimage_mem_nhds hVn, ?_⟩
  let E (i : S) : Set (P.pointMap ⁻¹' V) :=
    Subtype.val ⁻¹' (C.chart (P.chartIndex i.1) '' (P.chartPoint i.1 ⁻¹' D i))
  apply t2Space_of_finite_isClosed_cover E
  · intro i
    have hc := P.isClosed_chart_image_over_open i.1 isOpen_interior
      ((hDc i).isClosed.preimage (P.chartPoint i.1).continuous).isCompact
      (show (a.chart i.1 ∘ P.chartPoint i.1) '' (P.chartPoint i.1 ⁻¹' D i) ⊆ U from by
        rintro _ ⟨s, hs, rfl⟩
        exact hDU i ⟨_, hs, rfl⟩)
    exact hc.preimage (continuous_inclusion (preimage_mono hVU))
  · intro i
    have : T2Space (range (C.chart (P.chartIndex i.1))) :=
      (P.isEmbedding_chart i.1).toHomeomorph.t2Space
    let f : E i → range (C.chart (P.chartIndex i.1)) :=
      fun y => ⟨y.1.1, by obtain ⟨s, hs, heq⟩ := y.2; exact ⟨s, heq⟩⟩
    apply T2Space.of_injective_continuous (f := f)
    · intro y y' h
      exact Subtype.ext (Subtype.ext
        (congrArg (fun t : range (C.chart (P.chartIndex i.1)) => t.1) h))
    · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro y
    obtain ⟨V', hV', hyV'⟩ := y.2.1.2
    obtain ⟨i, rfl⟩ := hστ hV'
    let s : S := ⟨i, hV'⟩
    have hyi : y.1 ∈ range (C.chart (P.chartIndex i)) := by
      rw [P.range_chart]
      exact hyV'
    obtain ⟨t, ht⟩ := hyi
    refine ⟨s, t, ?_, ht⟩
    apply hWD s
    change a.chart i (P.chartPoint i t) ∈ W s
    rw [← P.pointMap_chart, ht]
    exact mem_iInter.1 y.2.2 s

/-- The range identity identifies the quotient chart family with the
continuous inverse image of the original net. -/
theorem isNet_chartFamily :
    AtlasTopology.IsNet (range fun i : a.Index => range (C.chart (P.chartIndex i))) := by
  have heq : (fun i : a.Index => range (C.chart (P.chartIndex i))) =
      (Set.preimage P.pointMap) ∘ (fun i : a.Index => range (a.chart i)) :=
    funext P.range_chart
  rw [heq, Set.range_comp]
  exact a.isNet_chartFamily.preimage_image P.pointMap.continuous

/-- The complete topological laws for the actual quotient chart system. -/
theorem topology : TopologyStatement.{u, v, w, u', w'} := by
  intro K _ _ _ L _ _ _ X _ a C P
  exact ⟨P.isEmbedding_chart, P.locallyHausdorff, P.isNet_chartFamily⟩

end AtlasProjection
end AffinoidChartSystem

end Langlands.Analytic
