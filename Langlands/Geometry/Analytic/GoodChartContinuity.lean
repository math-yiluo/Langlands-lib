import Langlands.Geometry.Analytic.ChartDomainSpectralTests
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralConvergence
import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover

/-! # Continuity of analytic actions from a finite cover by good charts -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology BanachSpectrum PresentedAffinoidAlgebra
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The strong inclusion of nested analytic domains commutes with the two
canonical inclusions. -/
theorem domainMap_comp_domainInclusion (S : SaturatedAtlasPresentation.{u, v, v} K)
    {D E : S.AnalyticDomain} (h : D ≤ E) :
    S.domainMap h ≫ S.domainInclusion E = S.domainInclusion D := by
  refine AffinoidAtlasPresentation.StrongHom.ext_of_saturated
    (S.domain D).hasAllLocalDomains ?_ ?_
  · ext x
    rfl
  · intro c
    have hc : (S.domainInclusion D).baseMap ''
        range ((S.domain D).presentation.atlas.chart c) ⊆
          range (S.presentation.atlas.chart c.val) := by
      rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    refine ⟨c.val, ?_, ?_⟩
    · rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · let c' : (S.domain E).presentation.atlas.Index := ⟨c.val, c.property.trans h⟩
      have h1 : (S.domainMap h).baseMap '' range ((S.domain D).presentation.atlas.chart c) ⊆
          range ((S.domain E).presentation.atlas.chart c') := by
        rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
      have h2 : (S.domainInclusion E).baseMap ''
          range ((S.domain E).presentation.atlas.chart c') ⊆
            range (S.presentation.atlas.chart c.val) := by
        rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
      refine (saturatedComp_pullback (S.domainMap h) (S.domainInclusion E)
        (S.domain D).hasAllLocalDomains (S.domain E).hasAllLocalDomains c c' c.val h1 h2
        _).trans ?_
      change (S.presentation.atlas.restriction c.val c.val _).comp
          (S.presentation.atlas.restriction c.val c.val _) =
        S.presentation.atlas.restriction c.val c.val _
      rw [S.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- A point of a chart lying in a smaller chart comes from the smaller chart's
spectrum through the atlas restriction. -/
theorem exists_restriction_comap_eq_aux (S : SaturatedAtlasPresentation.{u, v, v} K)
    {k i : S.presentation.atlas.Index}
    (h : range (S.presentation.atlas.chart k) ⊆ range (S.presentation.atlas.chart i))
    (p : BanachSpectrum (S.presentation.atlas.algebra i))
    (hp : S.presentation.atlas.chart i p ∈ range (S.presentation.atlas.chart k)) :
    ∃ p' : BanachSpectrum (S.presentation.atlas.algebra k),
      BanachSpectrum.comap (S.presentation.atlas.restriction k i h).toBoundedRingHom p' = p := by
  have : p ∈ range (BanachSpectrum.comap
      (S.presentation.atlas.restriction k i h).toBoundedRingHom) := by
    rw [S.presentation.atlas.range_restriction k i h]
    exact hp
  exact this

variable {X : LocalizedCategory.{u, v, v} (K := K)}

private theorem fullChart_contains (S : SaturatedAtlasPresentation.{u, v, v} K)
    (i : S.presentation.atlas.Index) (j : (S.domain (S.chartDomain i)).presentation.atlas.Index) :
    range ((S.domain (S.chartDomain i)).presentation.atlas.chart j) ⊆
      range ((S.domain (S.chartDomain i)).presentation.atlas.chart (chartDomainFullChart S i)) := by
  rw [(chartDomainFullChart_surjective S i).range_eq]
  exact subset_univ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The spectrum map of the pullback of a chart-preserving endomorphism is the
underlying map of the endomorphism on the chart. -/
theorem chart_comap_preservedChartPullback (φ : X ⟶ X)
    (i : (presentationOf X).presentation.atlas.Index)
    (hi : localizedSpaceFunctor.map φ ⁻¹' ((presentationOf X).chartDomain i).carrier =
      ((presentationOf X).chartDomain i).carrier)
    (x : BanachSpectrum ((presentationOf X).presentation.atlas.algebra i)) :
    (presentationOf X).presentation.atlas.chart i
        (BanachSpectrum.comap (preservedChartPullback i φ).toBoundedRingHom x) =
      localizedSpaceFunctor.map φ ((presentationOf X).presentation.atlas.chart i x) := by
  let S := presentationOf X
  let D := S.chartDomain i
  let ψ := domainRestrict D D φ (mapsTo_chart_of_preimage_eq i φ hi)
  let e := localizedTopTargetHomEquiv (A := S.domain D) (chartDomainFullChart S i)
    (fullChart_contains S i)
  let b : S.domain D ⟶ S.domain D := e.symm ψ
  have hb : localizationFunctor.map b = ψ := by
    simpa only [b, e, localizedTopTargetHomEquiv_apply] using e.apply_symm_apply ψ
  rw [preservedChartPullback_of_preimage_eq _ _ hi]
  change S.presentation.atlas.chart i (BanachSpectrum.comap
      (b.pullback (chartDomainFullChart S i) (chartDomainFullChart S i) _).toBoundedRingHom x) = _
  have hcomm := b.chart_comm (chartDomainFullChart S i) (chartDomainFullChart S i)
    (b.image_chart_top (chartDomainFullChart S i) (fullChart_contains S i)
      (chartDomainFullChart S i)) x
  have hval := congrArg Subtype.val hcomm
  refine hval.trans ?_
  have hψ : ∀ y : D.carrier, (localizedSpaceFunctor.map ψ y).val =
      localizedSpaceFunctor.map φ y.val := by
    intro y
    let y' : localizedSpaceFunctor.obj (domainObj X D) := y
    have h := congrArg (fun k : domainObj X D ⟶ X => localizedSpaceFunctor.map k y')
      (domainRestrict_comp D D φ (mapsTo_chart_of_preimage_eq i φ hi))
    simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at h
    exact h
  have hbase : ∀ y, b.baseMap y = localizedSpaceFunctor.map ψ y := by
    intro y
    rw [← hb, localizedSpaceFunctor_map]
    rfl
  rw [hbase, hψ]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullbacks of an endomorphism preserving two nested charts commute with the
atlas restriction between them. -/
theorem restriction_comp_preservedChartPullback (φ : X ⟶ X)
    {k i : (presentationOf X).presentation.atlas.Index}
    (hki : range ((presentationOf X).presentation.atlas.chart k) ⊆
      range ((presentationOf X).presentation.atlas.chart i))
    (hi : localizedSpaceFunctor.map φ ⁻¹' ((presentationOf X).chartDomain i).carrier =
      ((presentationOf X).chartDomain i).carrier)
    (hk : localizedSpaceFunctor.map φ ⁻¹' ((presentationOf X).chartDomain k).carrier =
      ((presentationOf X).chartDomain k).carrier) :
    ((presentationOf X).presentation.atlas.restriction k i hki).comp
        (preservedChartPullback i φ) =
      (preservedChartPullback k φ).comp
        ((presentationOf X).presentation.atlas.restriction k i hki) := by
  let S := presentationOf X
  let Di := S.chartDomain i
  let Dk := S.chartDomain k
  have hle : Dk ≤ Di := hki
  let ι : S.domain Dk ⟶ S.domain Di := S.domainMap hle
  let ψi := domainRestrict Di Di φ (mapsTo_chart_of_preimage_eq i φ hi)
  let ψk := domainRestrict Dk Dk φ (mapsTo_chart_of_preimage_eq k φ hk)
  let ei := localizedTopTargetHomEquiv (A := S.domain Di) (chartDomainFullChart S i)
    (fullChart_contains S i)
  let ek := localizedTopTargetHomEquiv (A := S.domain Dk) (chartDomainFullChart S k)
    (fullChart_contains S k)
  let bi : S.domain Di ⟶ S.domain Di := ei.symm ψi
  let bk : S.domain Dk ⟶ S.domain Dk := ek.symm ψk
  have hbi : localizationFunctor.map bi = ψi := by
    simpa only [bi, ei, localizedTopTargetHomEquiv_apply] using ei.apply_symm_apply ψi
  have hbk : localizationFunctor.map bk = ψk := by
    simpa only [bk, ek, localizedTopTargetHomEquiv_apply] using ek.apply_symm_apply ψk
  have hι : localizationFunctor.map ι ≫ domainι X Di = domainι X Dk := by
    change localizationFunctor.map ι ≫ localizationFunctor.map (S.domainInclusion Di) =
      localizationFunctor.map (S.domainInclusion Dk)
    rw [← Functor.map_comp, domainMap_comp_domainInclusion]
  have hcomm : ι ≫ bi = bk ≫ ι := by
    apply (localizedTopTargetHomEquiv (A := S.domain Dk) (chartDomainFullChart S i)
      (fullChart_contains S i)).injective
    simp only [localizedTopTargetHomEquiv_apply, Functor.map_comp, hbi, hbk]
    apply (cancel_mono (domainι X Di)).1
    rw [Category.assoc, domainRestrict_comp, ← Category.assoc, hι, Category.assoc, hι,
      domainRestrict_comp]
  have h := congrArg (fun f => f.pullbackAtTop (chartDomainFullChart S i)
    (fullChart_contains S i) (chartDomainFullChart S k)) hcomm
  rw [pullbackAtTop_comp ι bi (chartDomainFullChart S i) (chartDomainFullChart S i)
      (fullChart_contains S i) (fullChart_contains S i),
    pullbackAtTop_comp bk ι (chartDomainFullChart S k) (chartDomainFullChart S i)
      (fullChart_contains S k) (fullChart_contains S i)] at h
  rw [preservedChartPullback_of_preimage_eq _ _ hi, preservedChartPullback_of_preimage_eq _ _ hk]
  exact h

section GoodCharts

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- A chart is good for an action when every group element near the identity
preserves it and the restricted pullbacks converge spectrally to the identity
on every section of the chart algebra. -/
def IsGoodChart (σ : G →* Aut X) (c : (presentationOf X).presentation.atlas.Index) : Prop :=
  (∀ᶠ g in 𝓝 (1 : G), localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹'
      ((presentationOf X).chartDomain c).carrier = ((presentationOf X).chartDomain c).carrier) ∧
    ∀ a, SpectralConvergesOn (𝓝 (1 : G)) (fun g => preservedChartPullback c (σ g).asIso.hom)
      (BoundedAlgHom.id K _) a

omit [CompleteSpace K] in
private theorem comap_id_apply {A : PresentedAffinoidAlgebra K} (x : BanachSpectrum A) :
    BanachSpectrum.comap (BoundedAlgHom.id K A).toBoundedRingHom x = x :=
  BanachSpectrum.ext fun _ => rfl

/-- Every subchart of a good chart is good. -/
theorem IsGoodChart.of_subset {σ : G →* Aut X}
    {c k : (presentationOf X).presentation.atlas.Index} (hc : IsGoodChart σ c)
    (hkc : range ((presentationOf X).presentation.atlas.chart k) ⊆
      range ((presentationOf X).presentation.atlas.chart c)) :
    IsGoodChart σ k := by
  let S := presentationOf X
  let D := S.presentation.atlas.restrictionDomain k c hkc
  let res := S.presentation.atlas.restriction k c hkc
  have hpre : ∀ᶠ g in 𝓝 (1 : G), localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹'
      (S.chartDomain k).carrier = (S.chartDomain k).carrier := by
    filter_upwards [hc.1, D.eventually_comap_mem_locus_iff hc.2] with g hg hD
    ext y
    change localizedSpaceFunctor.map (σ g).asIso.hom y ∈ range (S.presentation.atlas.chart k) ↔
      y ∈ range (S.presentation.atlas.chart k)
    by_cases hy : y ∈ range (S.presentation.atlas.chart c)
    · obtain ⟨x, rfl⟩ := hy
      rw [← chart_comap_preservedChartPullback (σ g).asIso.hom c hg x]
      have := hD x
      rw [comap_id_apply] at this
      exact this
    · have hy' : y ∉ range (S.presentation.atlas.chart k) := fun h => hy (hkc h)
      have hgy :
          localizedSpaceFunctor.map (σ g).asIso.hom y ∉ range (S.presentation.atlas.chart c) := by
        intro h
        apply hy
        have h' : y ∈ localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹' (S.chartDomain c).carrier := h
        rw [hg] at h'
        exact h'
      exact ⟨fun h => absurd (hkc h) hgy, fun h => absurd h hy'⟩
  refine ⟨hpre, fun b => ?_⟩
  have hconv : ∀ a, SpectralConvergesOn (𝓝 (1 : G))
      (fun g => res.comp (preservedChartPullback c (σ g).asIso.hom))
        (res.comp (BoundedAlgHom.id K _)) a :=
    fun a => (hc.2 a).postcomp res
  have himg : HasImageIn K (res.comp (BoundedAlgHom.id K _)) D.locus := by
    intro x
    rw [BoundedAlgHom.comp_id]
    exact D.represents.hasImageIn x
  have hφD : ∀ᶠ g in 𝓝 (1 : G),
      (preservedChartPullback k (σ g).asIso.hom).comp D.baseMap =
        res.comp (preservedChartPullback c (σ g).asIso.hom) := by
    filter_upwards [hc.1, hpre] with g hg hgk
    exact (restriction_comp_preservedChartPullback (σ g).asIso.hom hkc hg hgk).symm
  have hψD : (BoundedAlgHom.id K _).comp D.baseMap = res.comp (BoundedAlgHom.id K _) := by
    rw [BoundedAlgHom.id_comp, BoundedAlgHom.comp_id]
    rfl
  exact D.spectralConvergesOn_of_factor hconv himg hφD hψD b

/-- A chart covered by finitely many good subcharts is good. -/
theorem IsGoodChart.of_finite_cover {σ : G →* Aut X}
    {W : (presentationOf X).presentation.atlas.Index}
    {t : Set (presentationOf X).presentation.atlas.Index} (ht : t.Finite)
    (hgood : ∀ j ∈ t, IsGoodChart σ j)
    (hsub : ∀ j ∈ t, range ((presentationOf X).presentation.atlas.chart j) ⊆
      range ((presentationOf X).presentation.atlas.chart W))
    (hcov : range ((presentationOf X).presentation.atlas.chart W) ⊆
      ⋃ j ∈ t, range ((presentationOf X).presentation.atlas.chart j)) :
    IsGoodChart σ W := by
  let S := presentationOf X
  have hW : range (S.presentation.atlas.chart W) =
      ⋃ j ∈ t, range (S.presentation.atlas.chart j) :=
    Subset.antisymm hcov (iUnion₂_subset hsub)
  have : Finite t := ht.to_subtype
  have hpre : ∀ᶠ g in 𝓝 (1 : G), localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹'
      (S.chartDomain W).carrier = (S.chartDomain W).carrier := by
    filter_upwards [Filter.eventually_all.mpr (fun j : t => (hgood j j.property).1)] with g hg
    have hy : ∀ z : S.presentation.space, z ∈ range (S.presentation.atlas.chart W) ↔
        ∃ j, ∃ _ : j ∈ t, z ∈ range (S.presentation.atlas.chart j) := fun z => by
      rw [hW, mem_iUnion₂]
    ext y
    constructor
    · intro h
      obtain ⟨j, hj, hjm⟩ := (hy (localizedSpaceFunctor.map (σ g).asIso.hom y)).1 h
      have hjm' : y ∈ localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹'
          ((presentationOf X).chartDomain j).carrier := hjm
      rw [hg ⟨j, hj⟩] at hjm'
      exact (hy y).2 ⟨j, hj, hjm'⟩
    · intro h
      obtain ⟨j, hj, hjy⟩ := (hy y).1 h
      have hjy' : y ∈ ((presentationOf X).chartDomain j).carrier := hjy
      rw [← hg ⟨j, hj⟩] at hjy'
      exact (hy (localizedSpaceFunctor.map (σ g).asIso.hom y)).2 ⟨j, hj, hjy'⟩
  refine ⟨hpre, fun f ε hε => ?_⟩
  filter_upwards [hpre, Filter.eventually_all.mpr (fun j : t => (hgood j j.property).1),
    Filter.eventually_all.mpr (fun j : t => (hgood j j.property).2
      (S.presentation.atlas.restriction j W (hsub j j.property) f) ε hε)] with g hg hgj hbound x
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcov ⟨x, rfl⟩)
  obtain ⟨x', hx'⟩ := exists_restriction_comap_eq_aux S (hsub j hj) x hxj
  rw [← hx']
  let res := S.presentation.atlas.restriction j W (hsub j hj)
  change x' (res (preservedChartPullback W (σ g).asIso.hom f - BoundedAlgHom.id K _ f)) ≤ ε
  rw [map_sub]
  have hnat := restriction_comp_preservedChartPullback (σ g).asIso.hom (hsub j hj) hg (hgj ⟨j, hj⟩)
  have e1 : res (preservedChartPullback W (σ g).asIso.hom f) =
      preservedChartPullback j (σ g).asIso.hom (res f) := by
    change (res.comp (preservedChartPullback W (σ g).asIso.hom)) f = _
    rw [hnat]
    rfl
  rw [e1]
  exact hbound ⟨j, hj⟩ x'

/-- Berkovich continuity from a finite cover by good charts: on a Hausdorff
analytic space, if finitely many charts cover the space and each is good, then
every chart is good, hence every test triple holds near the identity. -/
theorem isContinuousAction_of_goodCharts [T2Space (localizedSpaceFunctor.obj X)]
    {σ : G →* Aut X} {s : Set (presentationOf X).presentation.atlas.Index} (hs : s.Finite)
    (hgood : ∀ c ∈ s, IsGoodChart σ c)
    (hcov : ∀ y : (presentationOf X).presentation.space,
      ∃ c ∈ s, y ∈ range ((presentationOf X).presentation.atlas.chart c)) :
    IsContinuousAction σ := by
  intro τ
  let S := presentationOf X
  have : T2Space S.presentation.space := ‹T2Space (localizedSpaceFunctor.obj X)›
  have hcomp : ∀ c, IsCompact (range (S.presentation.atlas.chart τ.domain) ∩
      range (S.presentation.atlas.chart c)) := fun c =>
    (isCompact_range (S.presentation.atlas.isEmbedding_chart τ.domain).continuous).inter_right
      (isCompact_range (S.presentation.atlas.isEmbedding_chart c).continuous).isClosed
  choose σc hσfin hσsub hσin hσcov using fun c : s =>
    S.presentation.atlas.isNet_chartFamily.exists_finite_cover_of_subset_inter
      (mem_range_self τ.domain) (mem_range_self c.val) (hcomp c.val) subset_rfl
  let t : Set S.presentation.atlas.Index :=
    ⋃ c : s, (fun k => range (S.presentation.atlas.chart k)) ⁻¹' σc c
  have : Finite s := hs.to_subtype
  have ht : t.Finite := Set.finite_iUnion fun c =>
    (hσfin c).preimage S.presentation.atlas.chartDomain_injective.injOn
  have hW : IsGoodChart σ τ.domain := by
    apply IsGoodChart.of_finite_cover ht
    · intro k hk
      obtain ⟨c, hkc⟩ := mem_iUnion.mp hk
      exact (hgood c c.property).of_subset ((hσin c _ hkc).trans inter_subset_right)
    · intro k hk
      obtain ⟨c, hkc⟩ := mem_iUnion.mp hk
      exact (hσin c _ hkc).trans inter_subset_left
    · rintro y ⟨x, rfl⟩
      obtain ⟨c, hc, hyc⟩ := hcov (S.presentation.atlas.chart τ.domain x)
      obtain ⟨V, hV, hyV⟩ := hσcov ⟨c, hc⟩ ⟨⟨x, rfl⟩, hyc⟩
      obtain ⟨k, rfl⟩ := hσsub ⟨c, hc⟩ hV
      exact mem_iUnion₂.mpr ⟨k, mem_iUnion.mpr ⟨⟨c, hc⟩, hV⟩, hyV⟩
  filter_upwards [hW.1, hW.2 τ.function τ.bound τ.bound_pos] with g hg hb
  exact isNear_id_of_spectralBound_preservedChartPullback τ hg hb

end GoodCharts

end Langlands.Analytic.SaturatedAtlasPresentation
