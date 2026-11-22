import Langlands.Geometry.Analytic.FullRecognitionChartMorphisms
import Langlands.Geometry.Analytic.AffinoidQuotientPullbackDescent
import Langlands.Geometry.Analytic.LocalizedDomainBaseChange
import Langlands.Geometry.Analytic.QuasiIsoReverseRecognition
import Langlands.Geometry.Analytic.SaturatedRecognitionCospans
import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality

/-! # Recognized closed immersions from affinoid quotient tests -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open PresentedAffinoidAlgebra IndexedAffinoidAtlas SpaceAnalytification

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, u, u} K}

private abbrev chartIso (A : SaturatedAtlasPresentation.{u, u, u} K)
    (i : A.presentation.atlas.Index) :=
  localizationFunctor.mapIso (A.smallChartDomainIso i)

private theorem chartIso_hom_comp (A : SaturatedAtlasPresentation.{u, u, u} K)
    (i : A.presentation.atlas.Index) :
    (chartIso A i).hom ≫ domainι (localizationFunctor.obj A) (A.chartDomain i) =
      localizationFunctor.map (A.smallChartSpectrumInclusion i) :=
  (localizationFunctor.map_comp _ _).symm.trans
    (congrArg localizationFunctor.map (smallChartDomainIso_hom_comp_inclusion A i))

private theorem eqToHom_comp_domainι {X : LocalizedCategory.{u, u, u} (K := K)}
    {D E : (presentationOf X).AnalyticDomain} (h : D = E) :
    eqToHom (congrArg (domainObj X) h) ≫ domainι X E = domainι X D := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem isPullback_smallChart_of_preimage (f : A ⟶ B)
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (h : f.baseMap '' range (A.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart j))
    (hpre : range (A.presentation.atlas.chart i) = f.baseMap ⁻¹' range (B.presentation.atlas.chart j)) :
    IsPullback (localizationFunctor.map (A.smallChartSpectrumInclusion i))
      (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} _ _ (f.pullback i j h))
      (localizationFunctor.map f) (localizationFunctor.map (B.smallChartSpectrumInclusion j)) := by
  let X := localizationFunctor.obj A
  let Y := localizationFunctor.obj B
  let F := localizationFunctor.map f
  let D := B.chartDomain j
  let E := domainPreimage F D
  let jA := localizationFunctor.map (A.smallChartSpectrumInclusion i)
  let jB := localizationFunctor.map (B.smallChartSpectrumInclusion j)
  let p := SmallAffinoidSpectrum.localizedMapEquiv.{u, u} _ _ (f.pullback i j h)
  have hE : A.chartDomain i = E := by
    ext x
    change x ∈ range (A.presentation.atlas.chart i) ↔ localizedSpaceFunctor.map F x ∈
      range (B.presentation.atlas.chart j)
    rw [show localizedSpaceFunctor.map F = TopCat.ofHom f.baseMap from localizedSpaceFunctor_map f]
    exact (congrArg (fun S : Set A.presentation.space => x ∈ S) hpre).to_iff
  let e : localizationFunctor.obj (A.smallChartSpectrum i) ≅ domainObj X E :=
    chartIso A i ≪≫ eqToIso (congrArg (domainObj X) hE)
  have he : e.hom ≫ domainι X E = jA := by
    change ((chartIso A i).hom ≫ eqToHom (congrArg (domainObj X) hE)) ≫ domainι X E = _
    rw [Category.assoc, eqToHom_comp_domainι hE]
    exact chartIso_hom_comp A i
  have hb : (chartIso B j).hom ≫ domainι Y D = jB := chartIso_hom_comp B j
  have hp : jA ≫ F = p ≫ jB := localizedSmallChart_comp_map f i j h
  apply (domainPreimage_isPullback F D).of_iso' e (Iso.refl X) (chartIso B j) (Iso.refl Y)
  · exact he.trans (Category.comp_id _).symm
  · apply (cancel_mono (domainι Y D)).mp
    change (e.hom ≫ domainPreimageMap F D) ≫ domainι Y D =
      (p ≫ (chartIso B j).hom) ≫ domainι Y D
    rw [Category.assoc, domainPreimageMap_comp_inclusion, ← Category.assoc, he, Category.assoc, hb]
    exact hp
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · exact hb.trans (Category.comp_id _).symm

private theorem isAdmissibleEpi_of_affinoid_iso {R S T : PresentedAffinoidAlgebra K}
    (q : BoundedAlgHom K R S) (g : BoundedAlgHom K R T)
    (e : localizedAffinoidSpectrum T ≅ localizedAffinoidSpectrum S)
    (he : e.hom ≫ SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R S q =
      SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R T g)
    (hq : q.IsAdmissibleEpi) : g.IsAdmissibleEpi := by
  let ψ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} S T).symm e.hom
  let χ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} T S).symm e.inv
  have hψ : SmallAffinoidSpectrum.localizedMapEquiv.{u, u} S T ψ = e.hom :=
    Equiv.apply_symm_apply _ _
  have hχ : SmallAffinoidSpectrum.localizedMapEquiv.{u, u} T S χ = e.inv :=
    Equiv.apply_symm_apply _ _
  have hχψ : χ.comp ψ = BoundedAlgHom.id K S := by
    apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} S S).injective
    rw [SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} ψ χ, hψ, hχ, e.inv_hom_id,
      SmallAffinoidSpectrum.localizedMapEquiv_apply.{u, u}, SmallAffinoidSpectrum.map_id.{u, u},
      _root_.CategoryTheory.Functor.map_id]
  have hψχ : ψ.comp χ = BoundedAlgHom.id K T := by
    apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} T T).injective
    rw [SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} χ ψ, hψ, hχ, e.hom_inv_id,
      SmallAffinoidSpectrum.localizedMapEquiv_apply.{u, u}, SmallAffinoidSpectrum.map_id.{u, u},
      _root_.CategoryTheory.Functor.map_id]
  have hmap : ψ.comp q = g := by
    apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R T).injective
    rw [SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} q ψ, hψ]
    exact he
  let E := BoundedAlgEquiv.ofHomInv ψ χ
    (fun x => congrArg (fun f : BoundedAlgHom K S S => f x) hχψ)
    (fun x => congrArg (fun f : BoundedAlgHom K T T => f x) hψχ)
  rw [← hmap]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _ hq E.isAdmissibleEpi

set_option backward.isDefEq.respectTransparency false in
private theorem isClosedImmersion_saturation_of_quotientTests (f : A ⟶ B)
    (htests : ∀ (R : PresentedAffinoidAlgebra K) (a : localizedAffinoidSpectrum R ⟶
        localizationFunctor.obj B),
      Nonempty (AffinoidQuotientPullback R (localizationFunctor.map f) a)) :
    AffinoidAtlasPresentation.StrongHom.IsClosedImmersion
      (A := A.presentation) (B := B.presentation)
      ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f) := by
  let G : ofSaturation A.presentation ⟶ ofSaturation B.presentation :=
    (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f
  intro W
  let A₁ := recognitionSource f
  let B₁ := recognitionBase B
  let eA := localizedQuasiIso (recognitionSourceComparison f)
    (recognitionSourceComparison_isQuasiIso f)
  let eB := localizedQuasiIso (recognitionBaseComparison B)
    (recognitionBaseComparison_isQuasiIso B)
  let jB := localizationFunctor.map (B₁.smallChartSpectrumInclusion W)
  let a : localizedAffinoidSpectrum W.algebra ⟶ localizationFunctor.obj B := jB ≫ eB.inv
  obtain ⟨P⟩ := htests W.algebra a
  let s := SmallAffinoidSpectrum.localizedMapEquiv.{u, u} _ _ P.quotientMap
  let F := localizationFunctor.map f ≫ eB.hom
  let D := B₁.chartDomain W
  let E := domainPreimage F D
  have ha : a ≫ eB.hom = jB := by
    change (jB ≫ eB.inv) ≫ eB.hom = jB
    rw [Category.assoc, eB.inv_hom_id, Category.comp_id]
  have hD : (chartIso B₁ W).hom ≫ domainι (localizationFunctor.obj B₁) D = jB :=
    chartIso_hom_comp B₁ W
  have hmodel : IsPullback P.lift (s ≫ (chartIso B₁ W).hom)
      F (domainι (localizationFunctor.obj B₁) D) := by
    apply P.isPullback.of_iso (Iso.refl _) (Iso.refl _) (chartIso B₁ W) eB
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · exact (Category.id_comp _).symm
    · exact ha.trans hD.symm
  let hpb := domainPreimage_isPullback F D
  let e : localizationFunctor.obj (A.domain E) ≅ localizedAffinoidSpectrum P.quotientAlgebra :=
    hpb.isoIsPullback _ _ hmodel
  obtain ⟨V, hV⟩ := exists_recognized_locus_of_affinoid_iso E P.quotientAlgebra e
  have hVpre : V.locus = G.baseMap ⁻¹' W.locus := by
    rw [hV]
    ext x
    change localizedSpaceFunctor.map F x ∈ range W.chart ↔ G.baseMap x ∈ W.locus
    have hF : F = localizationFunctor.map (f ≫ recognitionBaseComparison B) :=
      (localizationFunctor.map_comp _ _).symm
    rw [hF, localizedSpaceFunctor_map, W.range_chart]
    rfl
  have hVW : G.baseMap '' range V.chart ⊆ range W.chart := by
    rw [V.range_chart, W.range_chart, hVpre]
    exact image_preimage_subset _ _
  let i : A₁.presentation.atlas.Index := ⟨V, W, hVW⟩
  let g := recognitionMap f
  have hpre : range (A₁.presentation.atlas.chart i) =
      g.baseMap ⁻¹' range (B₁.presentation.atlas.chart W) := by
    change range V.chart = G.baseMap ⁻¹' range W.chart
    rw [V.range_chart, W.range_chart, hVpre]
  let hrec := isPullback_smallChart_of_preimage g i W hVW hpre
  have hcomp : eA.hom ≫ localizationFunctor.map g = localizationFunctor.map f ≫ eB.hom :=
    (localizationFunctor.map_comp _ _).symm.trans
      ((congrArg localizationFunctor.map (recognitionMap_square f)).trans
        (localizationFunctor.map_comp _ _))
  have hmodel' : IsPullback (P.lift ≫ eA.hom) s (localizationFunctor.map g) jB := by
    apply P.isPullback.of_iso (Iso.refl _) eA (Iso.refl _) eB
    · simp only [Iso.refl_hom, Category.id_comp]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · exact hcomp.symm
    · exact ha.trans (Category.id_comp _).symm
  let eQ : localizedAffinoidSpectrum V.algebra ≅ localizedAffinoidSpectrum P.quotientAlgebra :=
    hrec.isoIsPullback _ _ hmodel'
  refine ⟨V, hVW, hVpre, isAdmissibleEpi_of_affinoid_iso P.quotientMap _ eQ ?_ ?_⟩
  · exact hrec.isoIsPullback_hom_snd _ _ hmodel'
  · exact @ClosedQuotient.map_isAdmissibleEpi K _ _ W.algebra P.ideal P.isClosed

set_option backward.isDefEq.respectTransparency false in
private theorem closedImmersion_map_of_quotientTests (f : A ⟶ B)
    (htests : ∀ (R : PresentedAffinoidAlgebra K) (a : localizedAffinoidSpectrum R ⟶
        localizationFunctor.obj B),
      Nonempty (AffinoidQuotientPullback R (localizationFunctor.map f) a)) :
    closedImmersion (localizationFunctor.map f) := by
  let G : ofSaturation A.presentation ⟶ ofSaturation B.presentation :=
    (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f
  refine ⟨A.presentation, B.presentation, G,
    isClosedImmersion_saturation_of_quotientTests f htests, ⟨?_⟩⟩
  refine Arrow.isoMk (localizationFunctor.mapIso A.saturationIso)
    (localizationFunctor.mapIso B.saturationIso) ?_
  change localizationFunctor.map A.saturationIso.hom ≫ localizationFunctor.map f =
    localizationFunctor.map G ≫ localizationFunctor.map B.saturationIso.hom
  have he : G ≫ B.saturationIso.hom = A.saturationIso.hom ≫ f := by
    change ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f) ≫
      B.saturationIso.hom = _
    rw [saturationExtension_eq_conjugate, Category.assoc, B.saturationIso.inv_hom_id,
      Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp, he]

set_option backward.isDefEq.respectTransparency false in
/-- Affinoid quotient pullbacks along every affinoid test give a closed
immersion in the localized category. -/
theorem closedImmersion_of_affinoidQuotientPullbacks
    {X Y : LocalizedCategory.{u, u, u} (K := K)} (F : X ⟶ Y)
    (htests : ∀ (R : PresentedAffinoidAlgebra K) (a : localizedAffinoidSpectrum R ⟶ Y),
      Nonempty (AffinoidQuotientPullback R F a)) : closedImmersion F := by
  obtain ⟨X₀, hX⟩ := localizedObjectEquiv.surjective X
  obtain ⟨Y₀, hY⟩ := localizedObjectEquiv.surjective Y
  change localizationFunctor.obj X₀ = X at hX
  change localizationFunctor.obj Y₀ = Y at hY
  subst X Y
  obtain ⟨S, s, hs, f, _, hf, _⟩ := exists_commonStrongNumerators F F
  let e := localizedQuasiIso s hs
  have hF : F = e.inv ≫ localizationFunctor.map f :=
    (e.inv_hom_id_assoc F).symm.trans (congrArg (e.inv ≫ ·) hf)
  have hlocal : closedImmersion (localizationFunctor.map f) := by
    apply closedImmersion_map_of_quotientTests f
    intro R a
    obtain ⟨P⟩ := htests R a
    refine ⟨⟨P.ideal, P.isClosed, P.lift ≫ e.inv, ?_⟩⟩
    apply P.isPullback.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id] using hF
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  rw [hF]
  exact MorphismProperty.RespectsIso.precomp closedImmersion e.inv _ hlocal

end Langlands.Analytic.SaturatedAtlasPresentation
