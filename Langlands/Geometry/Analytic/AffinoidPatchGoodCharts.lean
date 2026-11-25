import Langlands.Geometry.Analytic.ChartDomainSpectralTests
import Langlands.Geometry.Analytic.AffinoidPatchPullback
import Langlands.Geometry.Analytic.GoodChartContinuity
import Langlands.Geometry.Analytic.SaturatedLocalizedIsomorphisms

/-! # Good charts inside a patch with an affinoid model -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology BanachSpectrum PresentedAffinoidAlgebra
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}

/-- The underlying map of a strong map's localization is its base map. -/
private theorem map_localization_apply {A B : SaturatedAtlasPresentation.{u, v, v} K}
    (f : A ⟶ B) (x : A.presentation.space) :
    localizedSpaceFunctor.map (localizationFunctor.map f) x = f.baseMap x := by
  rw [localizedSpaceFunctor_map]
  rfl

omit [CompleteSpace K] in
private theorem comap_id_apply' {A : PresentedAffinoidAlgebra K} (x : BanachSpectrum A) :
    BanachSpectrum.comap (BoundedAlgHom.id K A).toBoundedRingHom x = x :=
  BanachSpectrum.ext fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The restriction of an endomorphism to an analytic domain acts on points as
the endomorphism itself. -/
theorem domainRestrict_apply_val (E : (presentationOf X).AnalyticDomain) (φ : X ⟶ X)
    (h : ∀ x ∈ E.carrier, localizedSpaceFunctor.map φ x ∈ E.carrier) (y : E.carrier) :
    (localizedSpaceFunctor.map (domainRestrict E E φ h) y).val =
      localizedSpaceFunctor.map φ y.val := by
  let y' : localizedSpaceFunctor.obj (domainObj X E) := y
  have h' := congrArg (fun k : domainObj X E ⟶ X => localizedSpaceFunctor.map k y')
    (domainRestrict_comp E E φ h)
  simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at h'
  exact h'

section Patch

variable (E : (presentationOf X).AnalyticDomain) {S₀ : SaturatedAtlasPresentation.{u, v, v} K}
  (t : S₀.presentation.atlas.Index)
  (ht : ∀ i, range (S₀.presentation.atlas.chart i) ⊆ range (S₀.presentation.atlas.chart t))
  (ι : localizationFunctor.obj S₀ ≅ domainObj X E)

/-- The complete strong map from the patch to its affinoid model underlying
the inverse of the model isomorphism. -/
def patchModelMap : (presentationOf X).domain E ⟶ S₀ :=
  (localizedTopTargetHomEquiv t ht).symm ι.inv

theorem localizationFunctor_map_patchModelMap :
    localizationFunctor.map (patchModelMap E t ht ι) = ι.inv := by
  have h := (localizedTopTargetHomEquiv t ht).apply_symm_apply ι.inv
  rwa [localizedTopTargetHomEquiv_apply] at h

/-- The strong map underlying a localized isomorphism is a strong
quasi-isomorphism. -/
theorem isQuasiIso_patchModelMap : (patchModelMap E t ht ι).IsQuasiIso := by
  have : IsIso (localizationFunctor.map (patchModelMap E t ht ι)) := by
    rw [localizationFunctor_map_patchModelMap]
    infer_instance
  exact isQuasiIso_of_isIso_localizationFunctor_map _

variable {E} in
/-- A chart of `X` inside the patch, as a chart of the patch. -/
def patchChart (W : (presentationOf X).presentation.atlas.Index)
    (hW : range ((presentationOf X).presentation.atlas.chart W) ⊆ E.carrier) :
    ((presentationOf X).domain E).presentation.atlas.Index :=
  ⟨W, hW⟩

/-- The affinoid domain of the model's greatest-chart algebra cut out by a
chart `W` of `X` lying inside the patch.  Its algebra is the chart algebra of
`W`, its structural map is the pullback of the model map, and its locus is the
image of `W` in the greatest chart of the model. -/
def patchChartDomain (W : (presentationOf X).presentation.atlas.Index)
    (hW : range ((presentationOf X).presentation.atlas.chart W) ⊆ E.carrier) :
    Domain K (S₀.presentation.atlas.algebra t) where
  algebra := (presentationOf X).presentation.atlas.algebra W
  baseMap := (patchModelMap E t ht ι).pullbackAtTop t ht (patchChart W hW)
  locus := (patchModelMap E t ht ι).chartImageLocus (patchChart W hW) t
  represents := (isQuasiIso_patchModelMap E t ht ι).2 _ _ _

variable {E t ht ι}

/-- A point of the patch lies on the chart `W` exactly when its coordinate on
the model's greatest chart lies in the locus of `patchChartDomain`. -/
theorem mem_range_chart_iff_mem_patchChartDomain_locus
    {W : (presentationOf X).presentation.atlas.Index}
    {hW : range ((presentationOf X).presentation.atlas.chart W) ⊆ E.carrier} (y : E.carrier)
    (x : BanachSpectrum (S₀.presentation.atlas.algebra t))
    (hx : S₀.presentation.atlas.chart t x = (patchModelMap E t ht ι).baseMap y) :
    y.val ∈ range ((presentationOf X).presentation.atlas.chart W) ↔
      x ∈ (patchChartDomain E t ht ι W hW).locus := by
  change _ ↔ S₀.presentation.atlas.chart t x ∈ (patchModelMap E t ht ι).baseMap ''
    range (((presentationOf X).domain E).presentation.atlas.chart (patchChart W hW))
  rw [hx]
  refine Iff.trans ?_ (Function.Injective.mem_set_image
    (isQuasiIso_patchModelMap E t ht ι).1.injective).symm
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The model map intertwines the restriction to the patch of a
patch-preserving endomorphism with the induced strong endomorphism of the
model. -/
theorem patchModelMap_baseMap_restrict (φ : X ⟶ X)
    (h : localizedSpaceFunctor.map φ ⁻¹' E.carrier = E.carrier) (y : E.carrier) :
    ((localizedTopTargetHomEquiv t ht).symm
        (patchConj E ι φ (mapsTo_of_preimage_eq E h))).baseMap
        ((patchModelMap E t ht ι).baseMap y) =
      (patchModelMap E t ht ι).baseMap
        (localizedSpaceFunctor.map (domainRestrict E E φ (mapsTo_of_preimage_eq E h)) y) := by
  let κ := patchModelMap E t ht ι
  let R := domainRestrict E E φ (mapsTo_of_preimage_eq E h)
  let b : S₀ ⟶ S₀ := (localizedTopTargetHomEquiv t ht).symm
    (patchConj E ι φ (mapsTo_of_preimage_eq E h))
  have hb : localizationFunctor.map b = patchConj E ι φ (mapsTo_of_preimage_eq E h) := by
    have h' := (localizedTopTargetHomEquiv t ht).apply_symm_apply
      (patchConj E ι φ (mapsTo_of_preimage_eq E h))
    rwa [localizedTopTargetHomEquiv_apply] at h'
  have hκ : localizationFunctor.map κ = ι.inv := localizationFunctor_map_patchModelMap E t ht ι
  have hcomm : localizationFunctor.map κ ≫ localizationFunctor.map b =
      R ≫ localizationFunctor.map κ := by
    rw [hb, hκ]
    simp only [patchConj, Iso.inv_hom_id_assoc, R]
  let y' : localizedSpaceFunctor.obj (domainObj X E) := y
  have h' := congrArg (fun k => localizedSpaceFunctor.map k y') hcomm
  simp only [Functor.map_comp, TopCat.comp_app] at h'
  rw [map_localization_apply, map_localization_apply, map_localization_apply] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The structural map of `patchChartDomain` is the pullback, to the greatest
chart of the model, of the composite of the inclusion of the chart into the
patch with the model map. -/
theorem pullbackAtTop_domainMap_comp_patchModelMap
    {W : (presentationOf X).presentation.atlas.Index}
    (hW : range ((presentationOf X).presentation.atlas.chart W) ⊆ E.carrier) :
    ((presentationOf X).domainMap (show (presentationOf X).chartDomain W ≤ E from hW) ≫
        patchModelMap E t ht ι).pullbackAtTop t ht
        (chartDomainFullChart (presentationOf X) W) =
      (patchChartDomain E t ht ι W hW).baseMap := by
  let S := presentationOf X
  have hle : S.chartDomain W ≤ E := hW
  let κ := patchModelMap E t ht ι
  have h1 : (S.domainMap hle).baseMap ''
      range ((S.domain (S.chartDomain W)).presentation.atlas.chart (chartDomainFullChart S W)) ⊆
        range ((S.domain E).presentation.atlas.chart (patchChart W hW)) := by
    rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  refine (saturatedComp_pullback (S.domainMap hle) κ (S.domain (S.chartDomain W)).hasAllLocalDomains
    (S.domain E).hasAllLocalDomains (chartDomainFullChart S W) (patchChart W hW) t h1
    (κ.image_chart_top t ht (patchChart W hW)) _).trans ?_
  change (S.presentation.atlas.restriction W W _).comp
      (κ.pullbackAtTop t ht (patchChart W hW)) = _
  rw [S.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a chart inside the patch, the chart pullback of an endomorphism
preserving both the patch and the chart is intertwined by the structural map
of `patchChartDomain` with its pullback to the model. -/
theorem preservedChartPullback_comp_patchChartDomain_baseMap (φ : X ⟶ X)
    {W : (presentationOf X).presentation.atlas.Index}
    (hW : range ((presentationOf X).presentation.atlas.chart W) ⊆ E.carrier)
    (hE : localizedSpaceFunctor.map φ ⁻¹' E.carrier = E.carrier)
    (hC : localizedSpaceFunctor.map φ ⁻¹' ((presentationOf X).chartDomain W).carrier =
      ((presentationOf X).chartDomain W).carrier) :
    (preservedChartPullback W φ).comp (patchChartDomain E t ht ι W hW).baseMap =
      (patchChartDomain E t ht ι W hW).baseMap.comp (patchPullback E t ht ι φ) := by
  let S := presentationOf X
  let C := S.chartDomain W
  have hle : C ≤ E := hW
  let κ := patchModelMap E t ht ι
  let j₀ : S.domain C ⟶ S₀ := S.domainMap hle ≫ κ
  let fullW := chartDomainFullChart S W
  have hfull := range_chart_subset_chartDomainFullChart S W
  have hκ : localizationFunctor.map κ = ι.inv := localizationFunctor_map_patchModelMap E t ht ι
  let ψC := domainRestrict C C φ (mapsTo_chart_of_preimage_eq W φ hC)
  let ψE := domainRestrict E E φ (mapsTo_of_preimage_eq E hE)
  let eC := localizedTopTargetHomEquiv (A := S.domain C) fullW hfull
  let bC : S.domain C ⟶ S.domain C := eC.symm ψC
  let b : S₀ ⟶ S₀ := (localizedTopTargetHomEquiv t ht).symm (patchConj E ι φ
    (mapsTo_of_preimage_eq E hE))
  have hbC : localizationFunctor.map bC = ψC := by
    simpa only [bC, eC, localizedTopTargetHomEquiv_apply] using eC.apply_symm_apply ψC
  have hb : localizationFunctor.map b = patchConj E ι φ (mapsTo_of_preimage_eq E hE) := by
    simpa only [b, localizedTopTargetHomEquiv_apply] using
      (localizedTopTargetHomEquiv t ht).apply_symm_apply
        (patchConj E ι φ (mapsTo_of_preimage_eq E hE))
  have hιC : localizationFunctor.map (S.domainMap hle) ≫ domainι X E = domainι X C := by
    change localizationFunctor.map (S.domainMap hle) ≫
        localizationFunctor.map (S.domainInclusion E) =
      localizationFunctor.map (S.domainInclusion C)
    rw [← Functor.map_comp, domainMap_comp_domainInclusion]
  have hres : ψC ≫ localizationFunctor.map (S.domainMap hle) =
      localizationFunctor.map (S.domainMap hle) ≫ ψE := by
    apply (cancel_mono (domainι X E)).1
    rw [Category.assoc, hιC, domainRestrict_comp, Category.assoc, domainRestrict_comp,
      ← Category.assoc, hιC]
  have hcomm : bC ≫ j₀ = j₀ ≫ b := by
    apply (localizedTopTargetHomEquiv (A := S.domain C) t ht).injective
    rw [localizedTopTargetHomEquiv_apply, localizedTopTargetHomEquiv_apply]
    show localizationFunctor.map (bC ≫ S.domainMap hle ≫ κ) =
      localizationFunctor.map ((S.domainMap hle ≫ κ) ≫ b)
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, hbC, hb, hκ]
    simp only [patchConj, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hres, Category.assoc]
  have h := congrArg (fun f => f.pullbackAtTop t ht fullW) hcomm
  rw [pullbackAtTop_comp bC j₀ fullW t hfull ht, pullbackAtTop_comp j₀ b t t ht ht,
    pullbackAtTop_domainMap_comp_patchModelMap hW] at h
  rw [preservedChartPullback_of_preimage_eq _ _ hC, patchPullback_of_preimage_eq E t ht ι _ hE]
  exact h

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- If the members of an action near the identity preserve a patch with an
affinoid model and their pullbacks to the model converge spectrally to the
identity, then they eventually preserve every chart inside the patch. -/
theorem eventually_preimage_chartDomain_of_affinoidPatch {σ : G →* Aut X}
    (hE : ∀ᶠ g in 𝓝 (1 : G),
      localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹' E.carrier = E.carrier)
    (hconv : ∀ a, SpectralConvergesOn (𝓝 (1 : G))
      (fun g => patchPullback E t ht ι (σ g).asIso.hom) (BoundedAlgHom.id K _) a)
    (W : (presentationOf X).presentation.atlas.Index)
    (hW : range ((presentationOf X).presentation.atlas.chart W) ⊆ E.carrier) :
    ∀ᶠ g in 𝓝 (1 : G), localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹'
      ((presentationOf X).chartDomain W).carrier =
        ((presentationOf X).chartDomain W).carrier := by
  filter_upwards [hE, (patchChartDomain E t ht ι W hW).eventually_comap_mem_locus_iff hconv]
    with g hg hD
  ext y
  change localizedSpaceFunctor.map (σ g).asIso.hom y ∈
      range ((presentationOf X).presentation.atlas.chart W) ↔
    y ∈ range ((presentationOf X).presentation.atlas.chart W)
  by_cases hy : y ∈ E.carrier
  · let y' : E.carrier := ⟨y, hy⟩
    obtain ⟨x, hx⟩ : (patchModelMap E t ht ι).baseMap y' ∈
        range (S₀.presentation.atlas.chart t) := by
      rw [range_greatestChart_eq_univ t ht]
      exact mem_univ _
    let R := domainRestrict E E (σ g).asIso.hom (mapsTo_of_preimage_eq E hg)
    let y'' : E.carrier := localizedSpaceFunctor.map R y'
    have hval : y''.val = localizedSpaceFunctor.map (σ g).asIso.hom y :=
      domainRestrict_apply_val E (σ g).asIso.hom (mapsTo_of_preimage_eq E hg) y'
    let b : S₀ ⟶ S₀ := (localizedTopTargetHomEquiv t ht).symm
      (patchConj E ι (σ g).asIso.hom (mapsTo_of_preimage_eq E hg))
    have hx'' : S₀.presentation.atlas.chart t (BanachSpectrum.comap
        (patchPullback E t ht ι (σ g).asIso.hom).toBoundedRingHom x) =
          (patchModelMap E t ht ι).baseMap y'' := by
      rw [patchPullback_of_preimage_eq E t ht ι _ hg]
      refine (b.chart_comm t t (b.image_chart_top t ht t) x).trans ?_
      rw [hx]
      exact patchModelMap_baseMap_restrict (σ g).asIso.hom hg y'
    have e1 := mem_range_chart_iff_mem_patchChartDomain_locus (hW := hW) y'' _ hx''
    have e2 := mem_range_chart_iff_mem_patchChartDomain_locus (hW := hW) y' x hx
    rw [hD x, comap_id_apply'] at e1
    have key := e1.trans e2.symm
    rw [hval] at key
    exact key
  · have h1 : y ∉ range ((presentationOf X).presentation.atlas.chart W) :=
      fun h => hy (hW h)
    have h2 : localizedSpaceFunctor.map (σ g).asIso.hom y ∉
        range ((presentationOf X).presentation.atlas.chart W) := by
      intro h
      apply hy
      have : y ∈ localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹' E.carrier := hW h
      rwa [hg] at this
    exact iff_of_false h2 h1

/-- Under the same hypotheses, the chart pullbacks on every chart inside the
patch converge spectrally to the identity. -/
theorem spectralConvergesOn_preservedChartPullback_of_affinoidPatch {σ : G →* Aut X}
    (hE : ∀ᶠ g in 𝓝 (1 : G),
      localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹' E.carrier = E.carrier)
    (hconv : ∀ a, SpectralConvergesOn (𝓝 (1 : G))
      (fun g => patchPullback E t ht ι (σ g).asIso.hom) (BoundedAlgHom.id K _) a)
    (W : (presentationOf X).presentation.atlas.Index)
    (hW : range ((presentationOf X).presentation.atlas.chart W) ⊆ E.carrier)
    (a : (presentationOf X).presentation.atlas.algebra W) :
    SpectralConvergesOn (𝓝 (1 : G)) (fun g => preservedChartPullback W (σ g).asIso.hom)
      (BoundedAlgHom.id K _) a := by
  let D := patchChartDomain E t ht ι W hW
  have hkey : ∀ᶠ g in 𝓝 (1 : G), (preservedChartPullback W (σ g).asIso.hom).comp D.baseMap =
      D.baseMap.comp (patchPullback E t ht ι (σ g).asIso.hom) := by
    filter_upwards [hE, eventually_preimage_chartDomain_of_affinoidPatch hE hconv W hW]
      with g hg hC
    exact preservedChartPullback_comp_patchChartDomain_baseMap (σ g).asIso.hom hW hg hC
  refine D.spectralConvergesOn_of_factor (l := 𝓝 (1 : G))
    (φ := fun g => (preservedChartPullback W (σ g).asIso.hom).comp D.baseMap) (ψ := D.baseMap)
    ?_ D.represents.hasImageIn (φD := fun g => preservedChartPullback W (σ g).asIso.hom)
    (Filter.Eventually.of_forall fun _ => rfl) (BoundedAlgHom.id_comp _) a
  intro c ε hε
  filter_upwards [(hconv c).postcomp D.baseMap ε hε, hkey] with g hg hk
  rw [hk]
  exact hg

/-- **Good charts inside a patch with an affinoid model.** Let `E` be an
analytic domain of `X` with an isomorphism `ι` from the localization of a
presentation `S₀` with greatest chart `t`. If the members of an action near
the identity preserve `E` and their pullbacks to the greatest chart of the
model converge spectrally to the identity, then every chart of `X` contained
in `E` is a good chart for the action. -/
theorem isGoodChart_of_affinoidPatch {σ : G →* Aut X}
    (hE : ∀ᶠ g in 𝓝 (1 : G),
      localizedSpaceFunctor.map (σ g).asIso.hom ⁻¹' E.carrier = E.carrier)
    (hconv : ∀ a, SpectralConvergesOn (𝓝 (1 : G))
      (fun g => patchPullback E t ht ι (σ g).asIso.hom) (BoundedAlgHom.id K _) a)
    (W : (presentationOf X).presentation.atlas.Index)
    (hW : range ((presentationOf X).presentation.atlas.chart W) ⊆ E.carrier) :
    IsGoodChart σ W :=
  ⟨eventually_preimage_chartDomain_of_affinoidPatch hE hconv W hW,
    spectralConvergesOn_preservedChartPullback_of_affinoidPatch hE hconv W hW⟩

end Patch

end Langlands.Analytic.SaturatedAtlasPresentation
