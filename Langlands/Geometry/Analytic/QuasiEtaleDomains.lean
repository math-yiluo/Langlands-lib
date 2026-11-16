import Langlands.Geometry.Analytic.QuasiEtaleSite
import Langlands.Geometry.Analytic.InvariantAnalyticDomains
import Langlands.Geometry.Analytic.QuotientStrongDomainLocalization

/-! # Quasi-étale canonical inclusions of analytic domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set IndexedAffinoidAtlas
open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Restrict an actual isomorphism to domains preserved by it and its inverse. -/
def domainRestrictIso {X Y : LocalizedCategory.{u, v, w} (K := K)} (e : X ≅ Y)
    (D : (presentationOf X).AnalyticDomain) (E : (presentationOf Y).AnalyticDomain)
    (hf : ∀ x ∈ D.carrier, localizedSpaceFunctor.map e.hom x ∈ E.carrier)
    (hi : ∀ y ∈ E.carrier, localizedSpaceFunctor.map e.inv y ∈ D.carrier) :
    domainObj X D ≅ domainObj Y E where
  hom := domainRestrict D E e.hom hf
  inv := domainRestrict E D e.inv hi
  hom_inv_id := by
    apply (cancel_mono (domainι X D)).1
    rw [Category.assoc, domainRestrict_comp, domainRestrict_comp_assoc,
      e.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (domainι Y E)).1
    rw [Category.assoc, domainRestrict_comp, domainRestrict_comp_assoc,
      e.inv_hom_id, Category.comp_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem domainRestrictIso_hom_inclusion
    {X Y : LocalizedCategory.{u, v, w} (K := K)} (e : X ≅ Y)
    (D : (presentationOf X).AnalyticDomain) (E : (presentationOf Y).AnalyticDomain)
    (hf : ∀ x ∈ D.carrier, localizedSpaceFunctor.map e.hom x ∈ E.carrier)
    (hi : ∀ y ∈ E.carrier, localizedSpaceFunctor.map e.inv y ∈ D.carrier) :
    (domainRestrictIso e D E hf hi).hom ≫ domainι Y E = domainι X D ≫ e.hom :=
  domainRestrict_comp D E e.hom hf

theorem eqToIso_hom_domainInclusion
    (S : SaturatedAtlasPresentation.{u, v, w} K) {D E : S.AnalyticDomain}
    (h : D = E) :
    (eqToIso (congrArg (fun F => localizationFunctor.obj (S.domain F)) h)).hom ≫
      S.localizedDomainInclusion E = S.localizedDomainInclusion D := by
  cases h
  simp

/-- An original chart of a domain is also an ambient chart, with the same
affinoid-domain inclusion after the two domain inclusions are composed. -/
theorem isAffinoidDomainEmbedding_domainInclusion_comp
    (S : SaturatedAtlasPresentation.{u, v, w} K) (D : S.AnalyticDomain)
    (c : (S.domain D).presentation.atlas.Index) :
    IsAffinoidDomainEmbedding
      ((S.domain D).localizedDomainInclusion ((S.domain D).chartDomain c) ≫
        S.localizedDomainInclusion D) := by
  change { i : S.presentation.atlas.Index //
    Set.range (S.presentation.atlas.chart i) ⊆ D.carrier } at c
  let U := (S.domain D).chartDomain c
  have h : D.subspaceExtend U = S.chartDomain c.val := by
    apply SetLike.coe_injective
    change Subtype.val '' Set.range ((S.domain D).presentation.atlas.chart c) =
      Set.range (S.presentation.atlas.chart c.val)
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨(S.domain D).presentation.atlas.chart c y, ⟨y, rfl⟩, rfl⟩
  let e :
      localizationFunctor.obj ((S.domain D).domain U) ≅
        localizationFunctor.obj (S.domain (D.subspaceExtend U)) :=
    SourceCategory.comparisonFunctor.mapIso
      (SourceCategory.domainNestedIso D U).symm
  have he : e.hom ≫ S.localizedDomainInclusion (D.subspaceExtend U) =
      (S.domain D).localizedDomainInclusion U ≫ S.localizedDomainInclusion D := by
    have hh := congrArg SourceCategory.comparisonFunctor.map
      (SourceCategory.domainNestedInverse_ambientInclusion (A := S) D U)
    have hD := S.comparisonFunctor_map_domainInclusion D
    have hU := (S.originalDomain D).comparisonFunctor_map_domainInclusion U
    have hE := S.comparisonFunctor_map_domainInclusion (D.subspaceExtend U)
    exact (congrArg (e.hom ≫ ·) hE).symm.trans
      ((SourceCategory.comparisonFunctor.map_comp _ _).symm.trans
        (hh.trans ((SourceCategory.comparisonFunctor.map_comp _ _).trans
          (congrArg₂ (· ≫ ·) hU hD))))
  let e' : localizationFunctor.obj (S.domain (D.subspaceExtend U)) ≅
      localizationFunctor.obj (S.domain (S.chartDomain c.val)) :=
    eqToIso (congrArg (fun E => localizationFunctor.obj (S.domain E)) h)
  have he' : e'.hom ≫ S.localizedDomainInclusion (S.chartDomain c.val) =
      S.localizedDomainInclusion (D.subspaceExtend U) := by
    exact eqToIso_hom_domainInclusion S h
  exact ⟨c.val, e ≪≫ e', by
    change _ = (e.hom ≫ e'.hom) ≫ S.localizedDomainInclusion (S.chartDomain c.val)
    exact ((Category.assoc _ _ _).trans
      ((congrArg (e.hom ≫ ·) he').trans he)).symm⟩

/-- A chart of the constructed saturation of a domain is an ambient affinoid
domain, after the actual saturation comparison and domain inclusion. -/
theorem isAffinoidDomainEmbedding_saturationChart_domainInclusion
    (S : SaturatedAtlasPresentation.{u, v, v} K) (D : S.AnalyticDomain)
    (i : (ofSaturation (S.domain D).presentation).presentation.atlas.Index) :
    IsAffinoidDomainEmbedding
      (((ofSaturation (S.domain D).presentation).localizedDomainInclusion
          ((ofSaturation (S.domain D).presentation).chartDomain i) ≫
        localizationFunctor.map (S.domain D).saturationIso.hom) ≫
        S.localizedDomainInclusion D) := by
  let N := S.domain D
  let N' := ofSaturation N.presentation
  obtain ⟨c, hc⟩ := N.hasAllLocalDomains.exists_chart
    (N.presentation.atlas.saturatedRepresentative i)
  have hci : Set.range (N.presentation.atlas.chart c) =
      Set.range (N'.presentation.atlas.chart i) :=
    hc.trans ((N.presentation.atlas.saturatedRepresentative_locus i).trans
      (N.presentation.atlas.range_saturatedChart i).symm)
  let e := localizationFunctor.mapIso N.saturationIso
  have hf : ∀ x ∈ (N'.chartDomain i).carrier,
      localizedSpaceFunctor.map e.hom x ∈ (N.chartDomain c).carrier := by
    intro x hx
    have he : localizedSpaceFunctor.map e.hom x = x := by
      change (localizationFunctor ⋙ localizedSpaceFunctor).map N.saturationIso.hom x = x
      rw [Functor.congr_hom (localizationFunctor_localizedSpaceFunctor (K := K))]
      rfl
    rw [he]
    change x ∈ Set.range (N.presentation.atlas.chart c)
    rw [hci]
    exact hx
  have hi : ∀ x ∈ (N.chartDomain c).carrier,
      localizedSpaceFunctor.map e.inv x ∈ (N'.chartDomain i).carrier := by
    intro x hx
    have he : localizedSpaceFunctor.map e.inv x = x := by
      change (localizationFunctor ⋙ localizedSpaceFunctor).map N.saturationIso.inv x = x
      rw [Functor.congr_hom (localizationFunctor_localizedSpaceFunctor (K := K))]
      rfl
    rw [he]
    change x ∈ Set.range (N'.presentation.atlas.chart i)
    rw [← hci]
    exact hx
  let ec := domainRestrictIso e (N'.chartDomain i) (N.chartDomain c) hf hi
  have ht : ec.hom ≫ N.localizedDomainInclusion (N.chartDomain c) =
      N'.localizedDomainInclusion (N'.chartDomain i) ≫
        localizationFunctor.map N.saturationIso.hom :=
    domainRestrictIso_hom_inclusion e _ _ hf hi
  have h := (isAffinoidDomainEmbedding_domainInclusion_comp S D c).iso_comp ec
  change IsAffinoidDomainEmbedding
    (ec.hom ≫ (N.localizedDomainInclusion (N.chartDomain c) ≫
      S.localizedDomainInclusion D)) at h
  exact (congrArg IsAffinoidDomainEmbedding
    ((Category.assoc ec.hom _ (S.localizedDomainInclusion D)).symm.trans
      (congrArg (· ≫ S.localizedDomainInclusion D) ht))).mp h

/-- The canonical inclusion of any actual analytic domain is quasi-étale. -/
theorem quasiEtale_localizedDomainInclusion
    (S : SaturatedAtlasPresentation.{u, v, v} K) (D : S.AnalyticDomain) :
    quasiEtale (S.localizedDomainInclusion D) := by
  let N := S.domain D
  let g : ofSaturation N.presentation ⟶ ofSaturation S.presentation :=
    N.saturationIso.hom ≫ S.domainInclusion D ≫ S.saturationIso.inv
  refine ⟨N.presentation, S.presentation, g, ?_, ⟨?_⟩⟩
  · intro y
    obtain ⟨σ, hσ, hστ, -, hnhds⟩ :=
      (ofSaturation N.presentation).presentation.atlas.isNet_chartFamily.1 y
    refine ⟨σ, hσ, hnhds, fun V hV => ?_⟩
    obtain ⟨i, rfl⟩ := hστ hV
    refine ⟨i, rfl, localizationFunctor.obj S,
      localizationFunctor.map S.saturationIso.inv,
      ((ofSaturation N.presentation).localizedDomainInclusion _ ≫
        localizationFunctor.map N.saturationIso.hom) ≫ S.localizedDomainInclusion D,
      etale_of_isIso _, isAffinoidDomainEmbedding_saturationChart_domainInclusion S D i,
      ?_⟩
    simp only [g, Functor.map_comp, localizedDomainInclusion, Category.assoc]
  · refine Arrow.isoMk (localizationFunctor.mapIso N.saturationIso)
      (localizationFunctor.mapIso S.saturationIso) ?_
    change localizationFunctor.map N.saturationIso.hom ≫
        localizationFunctor.map (S.domainInclusion D) =
      localizationFunctor.map g ≫ localizationFunctor.map S.saturationIso.hom
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg localizationFunctor.map
    simp only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The canonical domain inclusion for an arbitrary localized object is quasi-étale. -/
theorem quasiEtale_domainι (X : LocalizedCategory.{u, v, v} (K := K))
    (D : (presentationOf X).AnalyticDomain) : quasiEtale (domainι X D) :=
  quasiEtale_localizedDomainInclusion (presentationOf X) D

end Langlands.Analytic.SaturatedAtlasPresentation
