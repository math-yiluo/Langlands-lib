import Langlands.Geometry.Analytic.EtaleChartAgreement
import Langlands.Geometry.Analytic.FullRecognitionEtaleComposition
import Langlands.Geometry.Analytic.QuasiEtaleDomainIntersections
import Langlands.Geometry.Analytic.SaturatedDomainHomPresheaf

/-! # Local equality of analytic maps over an unramified morphism -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem localized_eq_of_relativeDomainCover
    {E A : SaturatedAtlasPresentation.{u, v, v} K} {ι : Type v}
    (D : E.AnalyticDomain) (C : ι → E.AnalyticDomain) (hCD : ∀ i, C i ≤ D)
    (hcov : AtlasTopology.LocallyRefines (range fun i => (C i).carrier) {D.carrier})
    {a b : localizationFunctor.obj (E.domain D) ⟶ localizationFunctor.obj A}
    (he : ∀ i, domainOrderMap (U := localizationFunctor.obj E) (hCD i) ≫ a =
      domainOrderMap (U := localizationFunctor.obj E) (hCD i) ≫ b) : a = b := by
  let F := SourceCategory.comparisonFunctor (K := K)
  let a₀ : SourceCategory.ofPresentation (E.originalDomain D) ⟶ SourceCategory.ofPresentation A :=
    F.preimage a
  let b₀ : SourceCategory.ofPresentation (E.originalDomain D) ⟶ SourceCategory.ofPresentation A :=
    F.preimage b
  have ha : F.map a₀ = a := F.map_preimage a
  have hb : F.map b₀ = b := F.map_preimage b
  have h : a₀ = b₀ := SourceCategory.eq_of_relativeDomainCover D C hCD hcov a₀ b₀ (by
    intro i
    apply F.map_injective
    have hi : F.map (SourceCategory.domainMap (hCD i)) =
        domainOrderMap (U := localizationFunctor.obj E) (hCD i) := by
      apply (cancel_mono (E.localizedDomainInclusion D)).1
      have hinc := congrArg F.map (SourceCategory.domainMap_inclusion (hCD i))
      rw [Functor.map_comp] at hinc
      change F.map (SourceCategory.domainMap (hCD i)) ≫
        SourceCategory.comparisonFunctor.map (SourceCategory.domainInclusion E D) =
        SourceCategory.comparisonFunctor.map (SourceCategory.domainInclusion E (C i)) at hinc
      rw [E.comparisonFunctor_map_domainInclusion, E.comparisonFunctor_map_domainInclusion] at hinc
      exact hinc.trans (domainOrderMap_comp_inclusion (U := localizationFunctor.obj E) (hCD i)).symm
    rw [Functor.map_comp, Functor.map_comp, hi, ha, hb]
    exact he i)
  exact ha.symm.trans ((congrArg F.map h).trans hb)

private theorem IsLocallyChartCovered.shrink_charts
    {E : SaturatedAtlasPresentation.{u, v, v} K} {S : Set E.presentation.space}
    {x : E.presentation.space} {Q : E.presentation.atlas.Index → Prop}
    (h : E.IsLocallyChartCovered (fun _ => True) S x)
    (hQ : ∀ i, x ∈ range (E.presentation.atlas.chart i) → range (E.presentation.atlas.chart i) ⊆ S →
      ∃ j, range (E.presentation.atlas.chart j) ⊆ range (E.presentation.atlas.chart i) ∧
        range (E.presentation.atlas.chart j) ∈ 𝓝[range (E.presentation.atlas.chart i)] x ∧ Q j) :
    E.IsLocallyChartCovered Q S x := by
  classical
  obtain ⟨I, hI, hm, N, hN, hc⟩ := h
  let : Finite I := hI.to_subtype
  have key (i : I) : ∃ (j : E.presentation.atlas.Index) (U : Set E.presentation.space),
      U ∈ 𝓝 x ∧ range (E.presentation.atlas.chart j) ⊆ range (E.presentation.atlas.chart i.val) ∧
      U ∩ range (E.presentation.atlas.chart i.val) ⊆ range (E.presentation.atlas.chart j) ∧ Q j := by
    obtain ⟨j, hji, hj, hq⟩ := hQ i.val (hm _ i.property).1 (hm _ i.property).2.1
    obtain ⟨U, hU, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hj
    exact ⟨j, U, hU, hji, hsub, hq⟩
  choose j U hU hji hj hq using key
  refine ⟨range j, finite_range j, ?_, N ∩ ⋂ i, U i, inter_mem hN (Filter.iInter_mem.mpr hU), ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨hj i ⟨mem_of_mem_nhds (hU i), (hm _ i.property).1⟩,
      (hji i).trans (hm _ i.property).2.1, hq i⟩
  · rintro y ⟨hy, hyN, hyU⟩
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hc ⟨hy, hyN⟩)
    let i' : I := ⟨i, hi⟩
    exact mem_iUnion₂.mpr ⟨j i', mem_range_self i', hj i' ⟨mem_iInter.mp hyU i', hyi⟩⟩

private theorem exists_open_eq_of_locallyChartCovered
    {E A : SaturatedAtlasPresentation.{u, v, v} K} (a b : E ⟶ A)
    {x : E.presentation.space} {H : Set E.presentation.space} [T2Space H]
    (hH : H ∈ 𝓝 x)
    (h : E.IsLocallyChartCovered (fun i => E.domainInclusion (E.chartDomain i) ≫ a =
      E.domainInclusion (E.chartDomain i) ≫ b) H x) :
    ∃ (O : Set E.presentation.space) (hO : IsOpen O), x ∈ O ∧
      E.localizedDomainInclusion (E.openDomain O hO) ≫ localizationFunctor.map a =
        E.localizedDomainInclusion (E.openDomain O hO) ≫ localizationFunctor.map b := by
  classical
  obtain ⟨I, hI, hi, N, hN, hcov⟩ := h
  let : Finite I := hI.to_subtype
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hH hN)
  let D := E.openDomain O hO
  let C (i : I) := E.chartDomain i.val ⊓ D
  have hCD (i : I) : C i ≤ D := inf_le_right
  let F (i : I) : Set O := Subtype.val ⁻¹' range (E.presentation.atlas.chart i.val)
  have hC (i : I) : (C i).carrier = range (E.presentation.atlas.chart i.val) ∩ O := rfl
  have hfamily : AtlasTopology.restrictedFamily (range fun i => (C i).carrier) O = range F := by
    ext S
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, _, rfl⟩
      refine ⟨i, Set.ext fun y => ?_⟩
      change y.val ∈ range (E.presentation.atlas.chart i.val) ↔ y.val ∈ (C i).carrier
      rw [hC]
      exact ⟨fun hy => ⟨hy, y.property⟩, And.left⟩
    · rintro ⟨i, rfl⟩
      refine ⟨(C i).carrier, ⟨i, rfl⟩, hCD i, ?_⟩
      ext y
      change y.val ∈ range (E.presentation.atlas.chart i.val) ↔ y.val ∈ (C i).carrier
      rw [hC]
      exact ⟨fun hy => ⟨hy, y.property⟩, And.left⟩
  have hq : AtlasTopology.IsQuasinet (range F) := by
    refine AtlasTopology.isQuasinet_of_finite_closedCover (range F) (finite_range F)
      Subset.rfl ?_ ?_
    · rintro _ ⟨i, rfl⟩
      let S : Set H := Subtype.val ⁻¹' range (E.presentation.atlas.chart i.val)
      have hc := isCompact_range (E.presentation.atlas.isEmbedding_chart i.val).continuous
      have hs : IsCompact S := Topology.IsInducing.subtypeVal.isCompact_preimage' hc
        (by simpa only [Subtype.range_coe] using (hi _ i.property).2.1)
      let e : O → H := fun y => ⟨y.val, (hOsub y.property).1⟩
      have he : Continuous e := continuous_subtype_val.subtype_mk _
      exact hs.isClosed.preimage he
    · apply eq_univ_of_forall
      intro y
      obtain ⟨i, hi', hy⟩ := mem_iUnion₂.mp (hcov (hOsub y.property))
      exact mem_sUnion.mpr ⟨F ⟨i, hi'⟩, ⟨⟨i, hi'⟩, rfl⟩, hy⟩
  have href : AtlasTopology.LocallyRefines (range fun i => (C i).carrier) {D.carrier} :=
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp (hfamily.symm ▸ hq)
  refine ⟨O, hO, hxO, localized_eq_of_relativeDomainCover D C hCD href ?_⟩
  intro i
  let E₀ := localizationFunctor.obj E
  have hle : C i ≤ E.chartDomain i.val := inf_le_left
  let j : domainObj E₀ (C i) ⟶ domainObj E₀ (E.chartDomain i.val) :=
    domainOrderMap (U := E₀) hle
  have he := congrArg localizationFunctor.map (hi _ i.property).2.2
  rw [Functor.map_comp, Functor.map_comp] at he
  change domainι E₀ (E.chartDomain i.val) ≫ localizationFunctor.map a =
    domainι E₀ (E.chartDomain i.val) ≫ localizationFunctor.map b at he
  have hj : j ≫ domainι E₀ (E.chartDomain i.val) = domainι E₀ (C i) :=
    domainOrderMap_comp_inclusion (U := E₀) hle
  change domainOrderMap (U := E₀) (hCD i) ≫
      (domainι E₀ D ≫ localizationFunctor.map a) =
    domainOrderMap (U := E₀) (hCD i) ≫
      (domainι E₀ D ≫ localizationFunctor.map b)
  rw [← Category.assoc, ← Category.assoc,
    domainOrderMap_comp_inclusion (U := E₀) (hCD i)]
  exact (congrArg (· ≫ localizationFunctor.map a) hj).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg (j ≫ ·) he).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ localizationFunctor.map b) hj))))

set_option linter.defProp false in
/-- Two strong maps over the same analytic map agree near any common full
field point at which the latter map is unramified over all affinoid pieces. -/
def exists_open_eq_of_unramifiedAtAllPieces
    {T A B : AffinoidAtlasPresentation.{u, v, v} K}
    {L : Type uL} [NormedField L] [NormedAlgebra K L]
    (a b : ofSaturation T ⟶ ofSaturation A) (f : ofSaturation A ⟶ ofSaturation B)
    (hab : a ≫ f = b ≫ f) (q : FieldPoint L (ofSaturation T).presentation)
    (hq : q.map a (ofSaturation T).hasAllLocalDomains = q.map b (ofSaturation T).hasAllLocalDomains)
    (hu : f.IsUnramifiedAtAllPieces (a.baseMap q.point)) :
    ∃ (O : Set T.space) (hO : IsOpen O), q.point ∈ O ∧
      (ofSaturation T).localizedDomainInclusion ((ofSaturation T).openDomain O hO) ≫
        localizationFunctor.map a =
      (ofSaturation T).localizedDomainInclusion ((ofSaturation T).openDomain O hO) ≫
        localizationFunctor.map b := by
  classical
  let E := ofSaturation T
  let y := a.baseMap q.point
  have hby : b.baseMap q.point = y := (congrArg FieldPoint.point hq).symm
  have hbase (z : T.space) : f.baseMap (a.baseMap z) = f.baseMap (b.baseMap z) :=
    congrArg (fun c : E ⟶ ofSaturation B => c.baseMap z) hab
  obtain ⟨V, U, hV, hU, hy, hfin, hpieces⟩ := hu
  obtain ⟨H, hH, hT2⟩ := T.atlas.locallyHausdorff q.point
  have hUx : f.baseMap y ∈ U := hfin.1 ⟨y, hy, rfl⟩
  obtain ⟨I, hI, hIW, hIN⟩ := B.atlas.exists_finite_recognized_nhds_subset
    (f.baseMap y) U (hU.mem_nhds hUx)
  let : Finite I := hI.to_subtype
  have hp (W : I) := hfin.2 W.val (hIW _ W.property).2
  choose P hPW hP hfP using hp
  let S (W : I) : Set T.space :=
    (a.baseMap ⁻¹' (P W).locus ∩ b.baseMap ⁻¹' (P W).locus) ∩ H
  have haP (W : I) : a.baseMap q.point ∈ range (P W).chart := by
    rw [(P W).range_chart, hP W]
    exact ⟨hy, (hIW _ W.property).1⟩
  have hbP (W : I) : b.baseMap q.point ∈ range (P W).chart := hby.symm ▸ haP W
  let Q (i : E.presentation.atlas.Index) := E.domainInclusion (E.chartDomain i) ≫ a =
    E.domainInclusion (E.chartDomain i) ≫ b
  have hloc (W : I) : E.IsLocallyChartCovered Q (S W) q.point := by
    let a' : E ⟶ ofFullRecognition A := a ≫ A.localDomainToFullRecognition
    let b' : E ⟶ ofFullRecognition A := b ≫ A.localDomainToFullRecognition
    have ha' := isLocallyChartCovered_preimage a' (P W) (haP W)
    have hb' := isLocallyChartCovered_preimage b' (P W) (hbP W)
    have ha₀ : E.IsLocallyChartCovered (fun _ => True) (a.baseMap ⁻¹' (P W).locus) q.point := by
      rw [← (P W).range_chart]
      exact ha'
    have hb₀ : E.IsLocallyChartCovered (fun _ => True) (b.baseMap ⁻¹' (P W).locus) q.point := by
      rw [← (P W).range_chart]
      exact hb'
    apply (((ha₀.inter hb₀).inter (isLocallyChartCovered_of_mem_nhds hH))).shrink_charts
    intro i hi hsub
    refine exists_chart_eq_over_unramifiedPiece a b f hab q hq i hi (P W) W.val (hPW W) (hfP W)
      (hpieces W.val (hIW _ W.property).2 (hIW _ W.property).1 (P W) (hPW W) (hP W)) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact (P W).range_chart.symm ▸ (hsub hz).1.1
    · rintro _ ⟨z, hz, rfl⟩
      exact (P W).range_chart.symm ▸ (hsub hz).1.2
  let N := (a.baseMap ⁻¹' V ∩ b.baseMap ⁻¹' V) ∩ (fun z => f.baseMap (a.baseMap z)) ⁻¹'
    (⋃ W ∈ I, W.locus)
  have hyb : b.baseMap q.point ∈ V := hby.symm ▸ hy
  have hN : N ∈ 𝓝 q.point := inter_mem
    (inter_mem ((hV.preimage a.baseMap.continuous).mem_nhds hy)
      ((hV.preimage b.baseMap.continuous).mem_nhds hyb))
    ((f.baseMap.continuous.comp a.baseMap.continuous).continuousAt.preimage_mem_nhds hIN)
  refine @exists_open_eq_of_locallyChartCovered K _ _ _ E (ofSaturation A) a b
    q.point H hT2 hH ?_
  refine isLocallyChartCovered_of_cover (Zs := S) (fun _ => inter_subset_right) hN ?_ hloc
  rintro z ⟨hzH, ⟨hza, hzb⟩, hz⟩
  obtain ⟨W, hWI, hzW⟩ := mem_iUnion₂.mp hz
  refine mem_iUnion.mpr ⟨⟨W, hWI⟩, ⟨⟨?_, ?_⟩, hzH⟩⟩
  · change a.baseMap z ∈ (P ⟨W, hWI⟩).locus
    rw [hP]
    exact ⟨hza, hzW⟩
  · change b.baseMap z ∈ (P ⟨W, hWI⟩).locus
    rw [hP]
    refine ⟨hzb, ?_⟩
    change f.baseMap (b.baseMap z) ∈ W.locus
    exact hbase z ▸ hzW

end Langlands.Analytic.SaturatedAtlasPresentation
