import Langlands.Geometry.Analytic.DomainEtaleFactorizations
import Langlands.Geometry.Analytic.QuasiEtaleFiniteChartCover
import Langlands.Geometry.Analytic.TopChartSpectralTests
import Langlands.Geometry.Analytic.SaturatedLocalizedIsomorphisms
import Langlands.Geometry.Analytic.StrongQuasiIsoDomainRestriction
import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality

/-! # Transport of affinoid charts along domain embeddings and isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Topology IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The underlying continuous map of the image of a strong map is its base map. -/
theorem localizedSpaceFunctor_map_localizationFunctor_map_apply
    {A B : SaturatedAtlasPresentation.{u, v, w} K} (f : A ⟶ B) (x : A.presentation.space) :
    localizedSpaceFunctor.map (localizationFunctor.map f) x = f.baseMap x := by
  rw [localizedSpaceFunctor_map]
  rfl

/-- A chart of the source of a strong domain embedding maps onto a chart of the target, and
the two chart domains are isomorphic over the embedding: the restriction of the embedding to
the two charts is a strong quasi-isomorphism. -/
theorem exists_chart_iso_of_isDomainEmbedding {N Q : SaturatedAtlasPresentation.{u, v, w} K}
    (t : N ⟶ Q) (ht : AffinoidAtlasPresentation.StrongHom.IsDomainEmbedding t)
    (c : N.presentation.atlas.Index) :
    ∃ d : Q.presentation.atlas.Index,
      Set.range (Q.presentation.atlas.chart d) =
          t.baseMap '' Set.range (N.presentation.atlas.chart c) ∧
        ∃ η : localizationFunctor.obj (N.domain (N.chartDomain c)) ≅
            localizationFunctor.obj (Q.domain (Q.chartDomain d)),
          η.hom ≫ Q.localizedDomainInclusion (Q.chartDomain d) =
            N.localizedDomainInclusion (N.chartDomain c) ≫ localizationFunctor.map t := by
  obtain ⟨m, hm⟩ := t.target_exists c
  obtain ⟨d, hd⟩ := Q.hasAllLocalDomains.exists_chart
    (⟨m, ht.localDomain c m hm⟩ : IndexedAffinoidAtlas.LocalDomain Q.presentation.atlas)
  have hdeq : Set.range (Q.presentation.atlas.chart d) =
      t.baseMap '' Set.range (N.presentation.atlas.chart c) := by
    rw [hd]
    change Q.presentation.atlas.chart m '' (Q.presentation.atlas.chart m ⁻¹'
      (t.baseMap '' Set.range (N.presentation.atlas.chart c))) = _
    exact Set.image_preimage_eq_of_subset hm
  have hmaps : t.MapsOriginalDomainCharts (N.chartDomain c) (Q.chartDomain d) := by
    intro c'
    refine ⟨⟨d, subset_rfl⟩, ?_⟩
    rw [hdeq]
    exact Set.image_mono c'.property
  let r : N.domain (N.chartDomain c) ⟶ Q.domain (Q.chartDomain d) :=
    t.restrictDomains (N.chartDomain c) (Q.chartDomain d) hmaps
  have hr : r.IsQuasiIso := by
    refine ⟨?_, ?_⟩
    · rw [isHomeomorph_iff_isEmbedding_surjective]
      refine ⟨?_, ?_⟩
      · refine (IsEmbedding.subtypeVal.of_comp_iff).mp ?_
        exact ht.1.comp IsEmbedding.subtypeVal
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx, rfl⟩ : y ∈ t.baseMap '' Set.range (N.presentation.atlas.chart c) :=
          hdeq ▸ hy
        exact ⟨⟨x, hx⟩, rfl⟩
    · intro c' d' hc'
      have hloc : AffinoidAtlasPresentation.StrongHom.chartImageLocus r c' d' =
          t.chartImageLocus c'.val d'.val :=
        t.restrictDomains_chartImageLocus (N.chartDomain c) (Q.chartDomain d) hmaps c' d'
      rw [hloc]
      exact ht.2 c'.val d'.val
        ((t.restrictDomainsBaseMap_admissible_iff _ _ hmaps c' d').mp hc')
  refine ⟨d, hdeq, localizedQuasiIso r hr, ?_⟩
  rw [localizedQuasiIso_hom]
  simp only [localizedDomainInclusion]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg localizationFunctor.map (restrictDomains_comp_domainInclusion t _ _ hmaps)

/-- A chart of `S` contained in a domain `D`, as a chart of the domain. -/
abbrev nestedChart (S : SaturatedAtlasPresentation.{u, v, w} K) (D : S.AnalyticDomain)
    (c : S.presentation.atlas.Index)
    (hc : Set.range (S.presentation.atlas.chart c) ⊆ D.carrier) :
    (S.domain D).presentation.atlas.Index :=
  (⟨c, hc⟩ : S.presentation.atlas.SubspaceChart D.carrier)

/-- The chart domain of a chart contained in a domain `D`, taken inside `D`, is isomorphic to
the chart domain taken in `S`, compatibly with the inclusions into `S`. -/
theorem exists_nestedChart_iso (S : SaturatedAtlasPresentation.{u, v, w} K)
    (D : S.AnalyticDomain) (c : S.presentation.atlas.Index)
    (hc : Set.range (S.presentation.atlas.chart c) ⊆ D.carrier) :
    ∃ n : localizationFunctor.obj
        ((S.domain D).domain ((S.domain D).chartDomain (nestedChart S D c hc))) ≅
        localizationFunctor.obj (S.domain (S.chartDomain c)),
      n.hom ≫ S.localizedDomainInclusion (S.chartDomain c) =
        (S.domain D).localizedDomainInclusion ((S.domain D).chartDomain (nestedChart S D c hc)) ≫
          S.localizedDomainInclusion D := by
  let U := (S.domain D).chartDomain (nestedChart S D c hc)
  have h : D.subspaceExtend U = S.chartDomain c := by
    apply SetLike.coe_injective
    change Subtype.val '' Set.range ((S.domain D).presentation.atlas.chart
      (nestedChart S D c hc)) = Set.range (S.presentation.atlas.chart c)
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨(S.domain D).presentation.atlas.chart (nestedChart S D c hc) y, ⟨y, rfl⟩, rfl⟩
  refine ⟨domainNestedLocalizationIso S D U ≪≫
    eqToIso (congrArg (fun E => localizationFunctor.obj (S.domain E)) h), ?_⟩
  rw [Iso.trans_hom, Category.assoc, eqToIso_hom_domainInclusion S h,
    domainNestedLocalizationIso_hom_inclusion]

/-- Restricting an affinoid domain embedding of an analytic domain `D` to a chart of the
ambient presentation contained in `D` gives an affinoid domain embedding. -/
theorem IsAffinoidDomainEmbedding.chart_comp (S : SaturatedAtlasPresentation.{u, v, v} K)
    (D : S.AnalyticDomain) {W : LocalizedCategory.{u, v, v} (K := K)}
    {j₀ : localizationFunctor.obj (S.domain D) ⟶ W} (hj₀ : IsAffinoidDomainEmbedding j₀)
    (c : S.presentation.atlas.Index)
    (hc : Set.range (S.presentation.atlas.chart c) ⊆ D.carrier)
    (m : localizationFunctor.obj (S.domain (S.chartDomain c)) ⟶
      localizationFunctor.obj (S.domain D))
    (hm : m ≫ S.localizedDomainInclusion D = S.localizedDomainInclusion (S.chartDomain c)) :
    IsAffinoidDomainEmbedding (m ≫ j₀) := by
  obtain ⟨i, ε, rfl⟩ := hj₀
  let P := presentationOf W
  let Q := P.domain (P.chartDomain i)
  let i₀ := chartDomainFullChart P i
  have hi₀ : ∀ k, Set.range (Q.presentation.atlas.chart k) ⊆
      Set.range (Q.presentation.atlas.chart i₀) := by
    intro k
    rw [(chartDomainFullChart_surjective P i).range_eq]
    exact Set.subset_univ _
  let t : S.domain D ⟶ Q := (localizedTopTargetHomEquiv i₀ hi₀).symm ε.hom
  have ht' : localizationFunctor.map t = ε.hom := by
    rw [← localizedTopTargetHomEquiv_apply i₀ hi₀, Equiv.apply_symm_apply]
  have : IsIso (localizationFunctor.map t) := by rw [ht']; infer_instance
  have ht : t.IsQuasiIso := isQuasiIso_of_isIso_localizationFunctor_map t
  obtain ⟨d, -, η, hη⟩ :=
    exists_chart_iso_of_isDomainEmbedding t ⟨ht.1.isEmbedding, ht.2⟩ (nestedChart S D c hc)
  obtain ⟨n, hn⟩ := exists_nestedChart_iso S D c hc
  have hm' : m = n.inv ≫
      (S.domain D).localizedDomainInclusion ((S.domain D).chartDomain (nestedChart S D c hc)) := by
    apply (cancel_mono (S.localizedDomainInclusion D)).1
    rw [hm, Category.assoc, ← hn, Iso.inv_hom_id_assoc]
  have key := isAffinoidDomainEmbedding_domainInclusion_comp P (P.chartDomain i) d
  have heq : m ≫ ε.hom ≫ P.localizedDomainInclusion (P.chartDomain i) =
      (n.symm ≪≫ η).hom ≫ (Q.localizedDomainInclusion (Q.chartDomain d) ≫
        P.localizedDomainInclusion (P.chartDomain i)) := by
    rw [hm', ← ht', Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
      reassoc_of% hη]
  have h2 := key.iso_comp (n.symm ≪≫ η)
  rw [← heq] at h2
  exact h2

/-- A compact analytic domain is covered by finitely many charts contained in it. -/
theorem exists_finite_charts_of_isCompact (S : SaturatedAtlasPresentation.{u, v, w} K)
    (D : S.AnalyticDomain) (hD : IsCompact D.carrier) :
    ∃ σ : Set (Set S.presentation.space), σ.Finite ∧
      (∀ V ∈ σ, ∃ i : S.presentation.atlas.Index,
        Set.range (S.presentation.atlas.chart i) = V ∧ V ⊆ D.carrier) ∧
      D.carrier ⊆ ⋃₀ σ := by
  have hloc := (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp D.is_domain
  choose σ hσf hσs hσm hσn using
    fun x (hx : x ∈ D.carrier) => hloc D.carrier (Set.mem_singleton _) x hx
  have hU : ∀ x (hx : x ∈ D.carrier), ∃ U ∈ 𝓝 x, U ∩ D.carrier ⊆ ⋃₀ σ x hx :=
    fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hσn x hx)
  choose U hUn hUs using hU
  obtain ⟨t, ht⟩ := hD.elim_nhds_subcover' U hUn
  refine ⟨⋃ x : t, σ x.1.1 x.1.2, Set.finite_iUnion fun x => hσf _ _, ?_, ?_⟩
  · intro V hV
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hV
    obtain ⟨i, rfl⟩ := hσs _ _ hx
    exact ⟨i, rfl, (hσm _ _ _ hx).1⟩
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    obtain ⟨V, hV, hyV⟩ := Set.mem_sUnion.mp (hUs _ _ ⟨hyx, hy⟩)
    exact Set.mem_sUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hV⟩, hyV⟩

end Langlands.Analytic.SaturatedAtlasPresentation
