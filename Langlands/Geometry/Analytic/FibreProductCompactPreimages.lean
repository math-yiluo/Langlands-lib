import Langlands.Geometry.Analytic.FibreProductLocalCharts
import Mathlib.Topology.Compactness.Compact

/-! # Hausdorff fibre products and compact preimages of compatible pairs -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FibreProduct

open Set Filter Topology AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-- The continuous map recording the two factor points of a quotient point. -/
def projectionPair : C((chartSystem f g).Space, A.space × B.space) :=
  ⟨fun z => (fst f g z, snd f g z), (continuous_fst f g).prodMk (continuous_snd f g)⟩

/-- Hausdorff factors suffice for separation in the glued fibre product. -/
theorem t2Space_chartSystem_of_factors [T2Space A.space] [T2Space B.space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) : T2Space (chartSystem f g).Space := by
  constructor
  intro x y hxy
  by_cases h : projectionPair f g x = projectionPair f g y
  · obtain ⟨U, V, W, hU, hV, hW, hUT, hVT, hWT, hxU, hxV, hUW, hVW⟩ :=
      exists_hausdorff_patches f g x
    let : T2Space U := hUT
    let : T2Space V := hVT
    let : T2Space W := hWT
    let : T2Space (patchSystem f g U V).Space :=
      t2Space_patchSystem f g hU hV hA hB hC hW hUW hVW
    let e := patchMap f g U V
    have he := isOpenEmbedding_patchSubsystem f g hA hB hU hV
    have hrange : range e = fst f g ⁻¹' U ∩ snd f g ⁻¹' V := by
      change range ((chartSystem f g).subsystemMap (patchPairs f g U V)
        (isDownwardClosed_patchPairs f g U V)) = _
      rw [(chartSystem f g).range_subsystemMap, subsystemSupport_patchPairs f g hA hB hU hV]
    have hp : fst f g x = fst f g y := congrArg Prod.fst h
    have hq : snd f g x = snd f g y := congrArg Prod.snd h
    have hx : x ∈ range e := hrange.symm ▸ ⟨hxU, hxV⟩
    have hy : y ∈ range e := by
      rw [hrange]
      change fst f g y ∈ U ∧ snd f g y ∈ V
      rw [← hp, ← hq]
      exact ⟨hxU, hxV⟩
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    obtain ⟨D, E, hD, hE, hxD, hyE, hDE⟩ :=
      t2_separation (show x' ≠ y' from fun hab => hxy (hx'.symm.trans ((congrArg e hab).trans hy')))
    refine ⟨e '' D, e '' E, he.isOpenMap D hD, he.isOpenMap E hE,
      ⟨x', hxD, hx'⟩, ⟨y', hyE, hy'⟩, Set.disjoint_left.2 ?_⟩
    rintro _ ⟨x₀, hx₀, rfl⟩ ⟨y₀, hy₀, heq⟩
    exact Set.disjoint_left.mp hDE hx₀ ((he.injective heq) ▸ hy₀)
  · obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation h
    exact ⟨projectionPair f g ⁻¹' U, projectionPair f g ⁻¹' V,
      hU.preimage (projectionPair f g).continuous, hV.preimage (projectionPair f g).continuous,
      hxU, hyV, Set.disjoint_left.2 (fun _ hu hv => Set.disjoint_left.mp hUV hu hv)⟩

private theorem exists_finite_charts_in_open
    {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
    (ha : a.HasAllLocalDomains) {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ I : Set a.Index, I.Finite ∧ (∀ i ∈ I, range (a.chart i) ⊆ U) ∧
      (⋃ i ∈ I, range (a.chart i)) ∈ 𝓝 x := by
  let d := a.subspaceAtlas U (ha.isOriginalChartDomain_of_isOpen hU)
  let x' : U := ⟨x, hx⟩
  obtain ⟨S, hS, hSd, _, hn⟩ := d.isNet_chartFamily.1 x'
  have hchoose (T : S) : ∃ i : d.Index, range (d.chart i) = T.val := hSd T.property
  choose i hi using hchoose
  let : Finite S := hS.to_subtype
  let I : Set a.Index := range (fun T : S => (i T).val)
  refine ⟨I, finite_range _, ?_, ?_⟩
  · rintro _ ⟨T, rfl⟩
    exact (i T).property
  · rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq x']
    apply Filter.mem_of_superset hn
    intro y hy
    obtain ⟨T, hT, hyT⟩ := mem_sUnion.mp hy
    have hy' : y ∈ range (d.chart (i ⟨T, hT⟩)) := by
      rw [hi]
      exact hyT
    obtain ⟨z, hz⟩ := hy'
    exact mem_iUnion₂.mpr ⟨_, ⟨⟨T, hT⟩, rfl⟩, z, congrArg Subtype.val hz⟩

private theorem isCompact_pair_patch
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) {W : Set C.space} (hW : IsOpen W) [T2Space W]
    {I : Set A.atlas.Index} (hI : I.Finite) {J : Set B.atlas.Index} (hJ : J.Finite)
    (hf : ∀ i ∈ I, f.baseMap '' range (A.atlas.chart i) ⊆ W)
    (hg : ∀ j ∈ J, g.baseMap '' range (B.atlas.chart j) ⊆ W) :
    IsCompact (projectionPair f g ⁻¹'
      ((⋃ i ∈ I, range (A.atlas.chart i)) ×ˢ (⋃ j ∈ J, range (B.atlas.chart j)))) := by
  let L (i : I) (j : J) := fst f g ⁻¹' range (A.atlas.chart i.val) ∩
    snd f g ⁻¹' range (B.atlas.chart j.val)
  have he : projectionPair f g ⁻¹'
      ((⋃ i ∈ I, range (A.atlas.chart i)) ×ˢ (⋃ j ∈ J, range (B.atlas.chart j))) =
      ⋃ i : I, ⋃ j : J, L i j := by
    ext z
    constructor
    · rintro ⟨hzI, hzJ⟩
      obtain ⟨i, hi, hzI⟩ := mem_iUnion₂.mp hzI
      obtain ⟨j, hj, hzJ⟩ := mem_iUnion₂.mp hzJ
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, mem_iUnion.mpr ⟨⟨j, hj⟩, ⟨hzI, hzJ⟩⟩⟩
    · intro hz
      obtain ⟨i, hz⟩ := mem_iUnion.mp hz
      obtain ⟨j, ha, hb⟩ := mem_iUnion.mp hz
      exact ⟨mem_iUnion₂.mpr ⟨i.val, i.property, ha⟩,
        mem_iUnion₂.mpr ⟨j.val, j.property, hb⟩⟩
  rw [he]
  let : Finite I := hI.to_subtype
  let : Finite J := hJ.to_subtype
  refine isCompact_iUnion fun i => isCompact_iUnion fun j => ?_
  obtain ⟨Q, hQ, _, hcov⟩ := exists_finite_pairs_in_open_base f g hA hB hC hW
    i.val j.val (hf i.val i.property) (hg j.val j.property)
  change IsCompact (fst f g ⁻¹' range (A.atlas.chart i.val) ∩
    snd f g ⁻¹' range (B.atlas.chart j.val))
  rw [hcov]
  exact hQ.isCompact_biUnion fun q _ => isCompact_range ((chartSystem f g).continuous_chart q)

/-- The inverse image of a compact set of compatible projected pairs is compact. -/
theorem isCompact_preimage_projectionPair [T2Space A.space] [T2Space B.space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) {S : Set (A.space × B.space)}
    (hS : IsCompact S) (hcomp : ∀ z ∈ S, f.baseMap z.1 = g.baseMap z.2) :
    IsCompact (projectionPair f g ⁻¹' S) := by
  have hlocal (z : S) : ∃ V : Set (A.space × B.space), V ∈ 𝓝 z.val ∧
      IsCompact (projectionPair f g ⁻¹' V) := by
    obtain ⟨W, hW, hzW, hWT⟩ := exists_open_hausdorff_neighborhood C.atlas (f.baseMap z.val.1)
    let : T2Space W := hWT
    obtain ⟨I, hI, hIW, hIn⟩ := exists_finite_charts_in_open A.atlas hA
      (hW.preimage f.baseMap.continuous) (show z.val.1 ∈ f.baseMap ⁻¹' W from hzW)
    have hzW' : z.val.2 ∈ g.baseMap ⁻¹' W := by
      change g.baseMap z.val.2 ∈ W
      rw [← hcomp z.val z.property]
      exact hzW
    obtain ⟨J, hJ, hJW, hJn⟩ := exists_finite_charts_in_open B.atlas hB
      (hW.preimage g.baseMap.continuous) hzW'
    refine ⟨(⋃ i ∈ I, range (A.atlas.chart i)) ×ˢ (⋃ j ∈ J, range (B.atlas.chart j)), ?_, ?_⟩
    · rw [nhds_prod_eq]
      exact Filter.prod_mem_prod hIn hJn
    · apply isCompact_pair_patch f g hA hB hC hW hI hJ
      · rintro i hi _ ⟨x, hx, rfl⟩
        exact hIW i hi hx
      · rintro j hj _ ⟨x, hx, rfl⟩
        exact hJW j hj hx
  choose V hV hVc using hlocal
  obtain ⟨s, hs⟩ := hS.elim_nhds_subcover' (fun x hx => V ⟨x, hx⟩)
    (fun x hx => hV ⟨x, hx⟩)
  have hclosed := hS.isClosed.preimage (projectionPair f g).continuous
  have hcover : projectionPair f g ⁻¹' S ⊆ ⋃ x ∈ s, projectionPair f g ⁻¹' V x := by
    intro z hz
    obtain ⟨x, hx, hzV⟩ := mem_iUnion₂.mp (hs hz)
    exact mem_iUnion₂.mpr ⟨x, hx, hzV⟩
  have hc := s.finite_toSet.isCompact_biUnion fun x _ => hVc x
  exact hc.of_isClosed_subset hclosed hcover

end Langlands.Analytic.FibreProduct
