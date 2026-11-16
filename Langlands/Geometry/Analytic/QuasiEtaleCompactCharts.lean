import Langlands.Geometry.Analytic.QuasiEtaleDomains
import Langlands.Geometry.Analytic.LocalizedDomainBaseChange
import Langlands.Geometry.Analytic.LocalActionLifts

/-! # Compact quasi-étale chart objects -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Transport an actual domain through an isomorphism using its literal inverse image. -/
def domainPreimageIso {X Y : LocalizedCategory.{u, v, w} (K := K)}
    (e : X ≅ Y) (D : (presentationOf Y).AnalyticDomain) :
    domainObj X (domainPreimage e.hom D) ≅ domainObj Y D :=
  domainRestrictIso e (domainPreimage e.hom D) D (fun _ hx => hx) (by
    intro y hy
    change localizedSpaceFunctor.map e.hom (localizedSpaceFunctor.map e.inv y) ∈ D.carrier
    have he := congrArg
      (fun k : Y ⟶ Y => localizedSpaceFunctor.map k y) e.inv_hom_id
    simp only [Functor.map_comp] at he
    exact (congrArg (fun z => z ∈ D.carrier) he).mpr hy)

@[reassoc (attr := simp)]
theorem domainPreimageIso_hom_inclusion
    {X Y : LocalizedCategory.{u, v, w} (K := K)}
    (e : X ≅ Y) (D : (presentationOf Y).AnalyticDomain) :
    (domainPreimageIso e D).hom ≫ domainι Y D =
      domainι X (domainPreimage e.hom D) ≫ e.hom :=
  domainRestrict_comp _ _ _ (fun _ hx => hx)

/-- An analytic domain of an étale space is quasi-étale over the base. -/
theorem quasiEtale_localizedDomainInclusion_comp_of_etale
    (S : SaturatedAtlasPresentation.{u, v, v} K) (D : S.AnalyticDomain)
    {Y : LocalizedCategory.{u, v, v} (K := K)}
    (f : localizationFunctor.obj S ⟶ Y) (hf : etale f) :
    quasiEtale (S.localizedDomainInclusion D ≫ f) := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let ex : localizationFunctor.obj (ofSaturation A) ≅ localizationFunctor.obj S :=
    Arrow.leftFunc.mapIso e
  let ey : localizationFunctor.obj (ofSaturation B) ≅ Y := Arrow.rightFunc.mapIso e
  let E : (ofSaturation A).AnalyticDomain := domainPreimage ex.hom D
  let N := (ofSaturation A).domain E
  let ec : localizationFunctor.obj N ≅ localizationFunctor.obj (S.domain D) :=
    domainPreimageIso ex D
  let g' : ofSaturation N.presentation ⟶ ofSaturation B :=
    N.saturationIso.hom ≫ (ofSaturation A).domainInclusion E ≫ g
  refine ⟨N.presentation, B, g', ?_, ⟨?_⟩⟩
  · intro y
    obtain ⟨σ, hσ, hστ, -, hnhds⟩ :=
      (ofSaturation N.presentation).presentation.atlas.isNet_chartFamily.1 y
    refine ⟨σ, hσ, hnhds, fun V hV => ?_⟩
    obtain ⟨i, rfl⟩ := hστ hV
    refine ⟨i, rfl, localizationFunctor.obj (ofSaturation A),
      localizationFunctor.map g,
      ((ofSaturation N.presentation).localizedDomainInclusion _ ≫
        localizationFunctor.map N.saturationIso.hom) ≫
        (ofSaturation A).localizedDomainInclusion E,
      etale_localizationFunctor_map g hg,
      isAffinoidDomainEmbedding_saturationChart_domainInclusion (ofSaturation A) E i,
      ?_⟩
    simp only [g', Functor.map_comp, localizedDomainInclusion, Category.assoc]
  · refine Arrow.isoMk ((localizationFunctor.mapIso N.saturationIso) ≪≫ ec) ey ?_
    have ht : ec.hom ≫ S.localizedDomainInclusion D =
        (ofSaturation A).localizedDomainInclusion E ≫ ex.hom :=
      domainPreimageIso_hom_inclusion ex D
    have hw : ex.hom ≫ f = localizationFunctor.map g ≫ ey.hom := e.hom.w
    change (localizationFunctor.map N.saturationIso.hom ≫ ec.hom) ≫
      (S.localizedDomainInclusion D ≫ f) = localizationFunctor.map g' ≫ ey.hom
    rw [Category.assoc, ← Category.assoc ec.hom, ht, Category.assoc,
      hw, Functor.map_comp, Functor.map_comp]
    simp only [localizedDomainInclusion, Category.assoc]

/-- The domain restriction formulation for arbitrary localized objects. -/
theorem quasiEtale_domainι_comp_of_etale
    {X Y : LocalizedCategory.{u, v, v} (K := K)}
    (D : (presentationOf X).AnalyticDomain) (f : X ⟶ Y) (hf : etale f) :
    quasiEtale (domainι X D ≫ f) :=
  quasiEtale_localizedDomainInclusion_comp_of_etale (presentationOf X) D f hf

/-- A chart embedding followed by an étale arrow is quasi-étale. -/
theorem quasiEtale_comp_of_isAffinoidDomainEmbedding_of_etale
    {U V W : LocalizedCategory.{u, v, v} (K := K)}
    (j : U ⟶ V) (hj : IsAffinoidDomainEmbedding j)
    (f : V ⟶ W) (hf : etale f) : quasiEtale (j ≫ f) := by
  obtain ⟨i, e, rfl⟩ := hj
  have h := quasiEtale_domainι_comp_of_etale ((presentationOf V).chartDomain i) f hf
  change quasiEtale ((e.hom ≫ domainι V ((presentationOf V).chartDomain i)) ≫ f)
  rw [Category.assoc]
  exact
    ((quasiEtale (K := K)).cancel_left_of_respectsIso e.hom
      (domainι V ((presentationOf V).chartDomain i) ≫ f)).mpr h

/-- A chart domain, viewed as an analytic space, is compact and Hausdorff. -/
theorem isCompactSpace_chartDomainObj
    (S : SaturatedAtlasPresentation.{u, v, v} K)
    (i : S.presentation.atlas.Index) :
    IsCompactSpace (localizationFunctor.obj (S.domain (S.chartDomain i))) := by
  have hc := S.isCompactDomain_chartDomain i
  exact ⟨isCompact_iff_compactSpace.mp hc.1, hc.2⟩

/-- The local quasi-étale chart factorization gives actual quasi-étale chart
objects over the target, without a general composition theorem. -/
theorem IsQuasiEtale.exists_local_quasiEtale_charts
    {A B : AffinoidAtlasPresentation.{u, v, v} K}
    {g : ofSaturation A ⟶ ofSaturation B} (hg : IsQuasiEtale g) (y : A.space) :
    ∃ σ : Set (Set A.space), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 y ∧
      ∀ V ∈ σ, ∃ i : (ofSaturation A).presentation.atlas.Index,
        Set.range ((ofSaturation A).presentation.atlas.chart i) = V ∧
        quasiEtale ((ofSaturation A).localizedDomainInclusion
          ((ofSaturation A).chartDomain i) ≫ localizationFunctor.map g) := by
  obtain ⟨σ, hf, hn, hs⟩ := hg y
  refine ⟨σ, hf, hn, fun V hV => ?_⟩
  obtain ⟨i, hi, W, f, j, hf, hj, ht⟩ := hs V hV
  exact ⟨i, hi, ht ▸ quasiEtale_comp_of_isAffinoidDomainEmbedding_of_etale j hj f hf⟩

end Langlands.Analytic.SaturatedAtlasPresentation
