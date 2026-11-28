import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.PairSystemLocalizedMorphisms
import Langlands.Geometry.Analytic.LocalizedDomainBaseChange
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartNeighborhoods
import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # Actual small chart morphisms of full recognition maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Set
open AffinoidAtlasPresentation PresentedAffinoidAlgebra

attribute [local instance] chartSpectrum_small

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, v} K}

/-- The actual localized inclusion of the small spectrum of an atlas chart. -/
abbrev localizedSmallChart (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) :
    localizationFunctor.obj (A.smallChartSpectrum i) ⟶ localizationFunctor.obj A :=
  localizationFunctor.map (A.smallChartSpectrumInclusion i)

/-- The small spectrum of an atlas chart as the associated analytic domain. -/
def localizedSmallChartDomainIso (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) :
    localizationFunctor.obj (A.smallChartSpectrum i) ≅
      localizationFunctor.obj (A.domain (A.chartDomain i)) :=
  localizationFunctor.mapIso (A.smallChartDomainIso i)

theorem localizedSmallChart_eq_domainInclusion (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) :
    localizedSmallChart A i =
      (A.localizedSmallChartDomainIso i).hom ≫ A.localizedDomainInclusion (A.chartDomain i) :=
  (congrArg localizationFunctor.map (smallChartDomainIso_hom_comp_inclusion A i).symm).trans
    (localizationFunctor.map_comp (A.smallChartDomainIso i).hom
      (A.originalDomainInclusion (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i)))

instance localizedSmallChart_mono (i : A.presentation.atlas.Index) :
    Mono (A.localizedSmallChart i) := by
  rw [A.localizedSmallChart_eq_domainInclusion i]
  infer_instance

theorem localizedSmallChart_range (i : A.presentation.atlas.Index) :
    range (localizedSpaceFunctor.map (A.localizedSmallChart i)) =
      range (A.presentation.atlas.chart i) := by
  rw [A.localizedSmallChart_eq_domainInclusion i, Functor.map_comp]
  let e : ↑(localizedSpaceFunctor.obj (localizationFunctor.obj (A.smallChartSpectrum i))) ≃ₜ
      (A.chartDomain i).carrier := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso
    (A.localizedSmallChartDomainIso i))
  let f : (A.chartDomain i).carrier → A.presentation.space :=
    localizedSpaceFunctor.map (A.localizedDomainInclusion (A.chartDomain i))
  change range (f ∘ e) = range (A.presentation.atlas.chart i)
  rw [e.surjective.range_comp]
  have hf : f = Subtype.val :=
    funext (A.localizedSpaceFunctor_map_localizedDomainInclusion (A.chartDomain i))
  rw [hf, Subtype.range_coe, A.chartDomain_carrier]

theorem localizedSmallChart_injective (i : A.presentation.atlas.Index) :
    Function.Injective (localizedSpaceFunctor.map (A.localizedSmallChart i)) := by
  rw [A.localizedSmallChart_eq_domainInclusion i, Functor.map_comp]
  let e : ↑(localizedSpaceFunctor.obj (localizationFunctor.obj (A.smallChartSpectrum i))) ≃ₜ
      (A.chartDomain i).carrier := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso
    (A.localizedSmallChartDomainIso i))
  let f : (A.chartDomain i).carrier → A.presentation.space :=
    localizedSpaceFunctor.map (A.localizedDomainInclusion (A.chartDomain i))
  change Function.Injective (f ∘ e)
  have hf : f = Subtype.val :=
    funext (A.localizedSpaceFunctor_map_localizedDomainInclusion (A.chartDomain i))
  rw [hf]
  exact Subtype.val_injective.comp e.injective

/-- A map with image in a chart factors through the chart's small spectrum. -/
theorem exists_factor_localizedSmallChart
    {Z : LocalizedCategory.{u, v, v} (K := K)} (a : Z ⟶ localizationFunctor.obj A)
    (i : A.presentation.atlas.Index)
    (ha : ∀ z, localizedSpaceFunctor.map a z ∈ range (A.presentation.atlas.chart i)) :
    ∃ l : Z ⟶ localizationFunctor.obj (A.smallChartSpectrum i),
      l ≫ A.localizedSmallChart i = a := by
  obtain ⟨l, hl⟩ := exists_localizedDomainLift (A.chartDomain i) a ha
  let e := A.localizedSmallChartDomainIso i
  refine ⟨l ≫ e.inv, ?_⟩
  rw [A.localizedSmallChart_eq_domainInclusion i, Category.assoc, Iso.inv_hom_id_assoc, hl]

set_option backward.isDefEq.respectTransparency false in
theorem localizedSmallChart_comp_map (f : A ⟶ B)
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (h : f.baseMap '' range (A.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart j)) :
    A.localizedSmallChart i ≫ localizationFunctor.map f =
      SmallAffinoidSpectrum.localizedMapEquiv.{u, v} _ _ (f.pullback i j h) ≫
        B.localizedSmallChart j := by
  let R := A.presentation.atlas.algebra i
  let S := B.presentation.atlas.algebra j
  let g := f.pullback i j h
  have h₁ := SmallAffinoidSpectrum.chartMap_comp R i (BoundedAlgHom.id K R) f j h
  have h₂ := SmallAffinoidSpectrum.map_comp_chartMap.{u, v} g j (BoundedAlgHom.id K S)
  rw [BoundedAlgHom.id_comp] at h₁
  rw [BoundedAlgHom.comp_id] at h₂
  exact (localizationFunctor.map_comp _ _).symm.trans
    ((congrArg localizationFunctor.map (h₁.trans h₂.symm)).trans
      (localizationFunctor.map_comp _ _))

set_option backward.isDefEq.respectTransparency false in
theorem localizedSmallChart_domain_comp (A : SaturatedAtlasPresentation.{u, v, v} K)
    (D : A.AnalyticDomain) (i : (A.domain D).presentation.atlas.Index) :
    (A.domain D).localizedSmallChart i ≫ A.localizedDomainInclusion D =
      A.localizedSmallChart i.val := by
  have hi : (A.domainInclusion D).baseMap '' range ((A.domain D).presentation.atlas.chart i) ⊆
      range (A.presentation.atlas.chart i.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have h := localizedSmallChart_comp_map (A.domainInclusion D) i i.val hi
  have hp : (A.domainInclusion D).pullback i i.val hi =
      BoundedAlgHom.id K (A.presentation.atlas.algebra i.val) :=
    A.presentation.atlas.restriction_id i.val _
  rw [hp] at h
  exact h.trans (congrArg (fun t => t ≫ A.localizedSmallChart i.val)
    ((congrArg localizationFunctor.map (SmallAffinoidSpectrum.map_id.{u, v}
      (A.presentation.atlas.algebra i.val))).trans (localizationFunctor.map_id _)) |>.trans
        (Category.id_comp _))

section Recognition

/-- The spectrum of a recognized chart is small in its ambient space universe. -/
theorem recognizedChartSpectrum_small {X : Type v} [TopologicalSpace X]
    {a : IndexedAffinoidAtlas.{u, v, w} K X} (V : a.saturatedAtlas.RecognizedSubset) :
    Small.{v} (BanachSpectrum V.algebra) :=
  small_of_injective V.isEmbedding_chart.injective

attribute [local instance] recognizedChartSpectrum_small

variable {P Q : AffinoidAtlasPresentation.{u, v, v} K}
  (g : StrongHom P.saturatedPresentation Q.saturatedPresentation)

set_option backward.isDefEq.respectTransparency false in
/-- A restriction between recognized charts gives their triangle of inclusions. -/
theorem localizedSmallChart_restriction
    (V W : P.atlas.saturatedAtlas.RecognizedSubset) (h : V.locus ⊆ W.locus) :
    SmallAffinoidSpectrum.localizedMapEquiv.{u, v} _ _ (V.restriction W h) ≫
        (ofFullRecognition P).localizedSmallChart W =
      (ofFullRecognition P).localizedSmallChart V := by
  have hi : (𝟙 (ofFullRecognition P) : ofFullRecognition P ⟶ ofFullRecognition P).baseMap ''
      range V.chart ⊆ range W.chart := by
    change id '' range V.chart ⊆ range W.chart
    rw [image_id, V.range_chart, W.range_chart]
    exact h
  have hc := localizedSmallChart_comp_map (𝟙 (ofFullRecognition P)) V W hi
  change (ofFullRecognition P).localizedSmallChart V ≫
      localizationFunctor.map (𝟙 (ofFullRecognition P)) = _ at hc
  rw [localizationFunctor.map_id, Category.comp_id] at hc
  exact hc.symm

set_option backward.isDefEq.respectTransparency false in
theorem localizedSmallChart_comp_fullRecognition
    (V : P.atlas.saturatedAtlas.RecognizedSubset) (W : Q.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' range V.chart ⊆ range W.chart) :
    (ofFullRecognition P).localizedSmallChart V ≫ g.fullRecognitionLocalizedHom =
      SmallAffinoidSpectrum.localizedMapEquiv.{u, v} W.algebra V.algebra
        (g.fullRecognitionPairs.pullback V W h) ≫ (ofFullRecognition Q).localizedSmallChart W := by
  let p := g.fullRecognitionPairs
  let hp := g.fullRecognitionPairs_localCondition
  let N := admissibleNet (A := ofFullRecognition P) (B := ofFullRecognition Q) p hp
  let k : N.presentation.atlas.Index := ⟨V, W, h⟩
  let a := admissibleNetInclusion (A := ofFullRecognition P) (B := ofFullRecognition Q) p hp
  let b := admissibleNetMap (A := ofFullRecognition P) (B := ofFullRecognition Q) p hp
  have hk : a.baseMap '' range (N.presentation.atlas.chart k) ⊆
      range ((ofFullRecognition P).presentation.atlas.chart V) := by
    change (id : P.space → P.space) '' range V.chart ⊆ range V.chart
    rw [image_id]
  have ha := localizedSmallChart_comp_map a k V hk
  have hId : a.pullback k V hk = BoundedAlgHom.id K V.algebra := V.restriction_self
  have hChart : N.localizedSmallChart k ≫ localizationFunctor.map a =
      (ofFullRecognition P).localizedSmallChart V :=
    ha.trans ((congrArg (fun t => SmallAffinoidSpectrum.localizedMapEquiv.{u, v}
      V.algebra V.algebra t ≫ (ofFullRecognition P).localizedSmallChart V) hId).trans
      ((congrArg (fun t => t ≫ (ofFullRecognition P).localizedSmallChart V)
        ((congrArg localizationFunctor.map (SmallAffinoidSpectrum.map_id.{u, v} V.algebra)).trans
          (localizationFunctor.map_id _))).trans (Category.id_comp _)))
  have hNet : localizationFunctor.map a ≫ g.fullRecognitionLocalizedHom =
      localizationFunctor.map b :=
    localizationFunctor_map_admissibleNetInclusion_comp
      (A := ofFullRecognition P) (B := ofFullRecognition Q) p hp
  calc
    _ = (N.localizedSmallChart k ≫ localizationFunctor.map a) ≫ g.fullRecognitionLocalizedHom :=
      congrArg (· ≫ g.fullRecognitionLocalizedHom) hChart.symm
    _ = N.localizedSmallChart k ≫ localizationFunctor.map b := (Category.assoc _ _ _).trans
      (congrArg (N.localizedSmallChart k ≫ ·) hNet)
    _ = _ := localizedSmallChart_comp_map b k W h

theorem localizedSpaceFunctor_map_fullRecognition :
    localizedSpaceFunctor.map g.fullRecognitionLocalizedHom = TopCat.ofHom g.baseMap :=
  localizedSpaceFunctor_map_pairSystemLocalizedHom
    (A := ofFullRecognition P) (B := ofFullRecognition Q)
    g.fullRecognitionPairs g.fullRecognitionPairs_localCondition

/-- The canonical comparison from the local-domain enlargement to full recognition. -/
def fullRecognitionIso (P : AffinoidAtlasPresentation.{u, v, v} K) :
    localizationFunctor.obj (ofSaturation P) ≅ localizationFunctor.obj (ofFullRecognition P) :=
  localizedQuasiIso (StrongHom.localDomainToFullRecognitionHom P)
    P.localDomainToFullRecognition_isQuasiIso

theorem fullRecognitionIso_naturality :
    (fullRecognitionIso P).hom ≫ g.fullRecognitionLocalizedHom =
      localizationFunctor.map (show ofSaturation P ⟶ ofSaturation Q from g) ≫
        (fullRecognitionIso Q).hom :=
  g.localizationFunctor_map_comp_fullRecognitionLocalizedHom.trans
    (localizationFunctor.map_comp (show ofSaturation P ⟶ ofSaturation Q from g)
      (StrongHom.localDomainToFullRecognitionHom Q))

theorem etale_fullRecognition_iff :
    etale g.fullRecognitionLocalizedHom ↔ g.IsEtaleAllPieces :=
  ((etale (K := K)).cancel_left_of_respectsIso (fullRecognitionIso P).hom _).symm.trans
    ((congrArg (fun m => etale m) (fullRecognitionIso_naturality g)).to_iff.trans
      (((etale (K := K)).cancel_right_of_respectsIso _ (fullRecognitionIso Q).hom).trans
        (etale_localizationFunctor_map_ofSaturation_iff g)))

theorem fullRecognition_comp {R : AffinoidAtlasPresentation.{u, v, v} K}
    (f : StrongHom Q.saturatedPresentation R.saturatedPresentation) :
    g.fullRecognitionLocalizedHom ≫ f.fullRecognitionLocalizedHom =
      (g.saturatedComp f P.atlas.saturatedAtlas_hasAllLocalDomains
        Q.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionLocalizedHom := by
  apply (cancel_epi (fullRecognitionIso P).hom).mp
  have h := fullRecognitionIso_naturality
    (g.saturatedComp f P.atlas.saturatedAtlas_hasAllLocalDomains
      Q.atlas.saturatedAtlas_hasAllLocalDomains)
  change _ = localizationFunctor.map
    ((show ofSaturation P ⟶ ofSaturation Q from g) ≫
      (show ofSaturation Q ⟶ ofSaturation R from f)) ≫ (fullRecognitionIso R).hom at h
  rw [← Category.assoc, fullRecognitionIso_naturality, Category.assoc,
    fullRecognitionIso_naturality, ← Category.assoc, ← localizationFunctor.map_comp, h]

end Recognition

end Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Set
open PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : SaturatedAtlasPresentation.{u, v, v} K}

set_option backward.isDefEq.respectTransparency false in
/-- An affinoid spectrum identifying a localized analytic domain recognizes its locus. -/
theorem exists_recognized_locus_of_affinoid_iso (D : A.AnalyticDomain)
    (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]
    (e : localizationFunctor.obj (A.domain D) ≅
      localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} R)) :
    ∃ W : A.presentation.atlas.saturatedAtlas.RecognizedSubset, W.locus = D.carrier := by
  let S := SmallAffinoidSpectrum.saturated.{u, v} R
  let i := SmallAffinoidSpectrum.topIndex.{u, v} R
  let t := localizedTopTargetHomEquiv (A := A.domain D) (B := S) i
    (SmallAffinoidSpectrum.top_contains R)
  let m : A.domain D ⟶ S := t.symm e.hom
  have hm : localizationFunctor.map m = e.hom :=
    (localizedTopTargetHomEquiv_apply i (SmallAffinoidSpectrum.top_contains R) m).symm.trans
      (t.apply_symm_apply e.hom)
  let : IsIso (localizationFunctor.map m) := hm.symm ▸ e.isIso_hom
  let hq := isQuasiIso_of_isIso_localizationFunctor_map m
  let hc := m.hasCoherentPullbacks_of_saturated (A.domain D).hasAllLocalDomains
  let Q : S.presentation.atlas.saturatedAtlas.RecognizedSubset :=
    S.presentation.atlas.saturatedAtlas.originalRecognitionIndex
      (S.presentation.atlas.originalSaturatedIndex i)
  have hQ : Q.locus = univ :=
    (S.presentation.atlas.saturatedAtlas_original_range i).trans
      (SmallAffinoidSpectrum.range_topIndex R)
  let V := hq.reverseRecognizedImage hc S.hasAllLocalDomains Q
  have hV : V.locus = univ := by
    change (hq.reverseRecognizedImage hc S.hasAllLocalDomains Q).locus = univ
    rw [hq.reverseRecognizedImage_locus, hQ, preimage_univ]
  let j := A.domainInclusion D
  let hj := domainInclusion_isDomainEmbedding A D
  let hjc := j.hasCoherentPullbacks_of_saturated (A.domain D).hasAllLocalDomains
  refine ⟨hj.recognizedImage hjc V, ?_⟩
  rw [hj.recognizedImage_locus hjc V, hV]
  change Subtype.val '' (univ : Set D.carrier) = D.carrier
  rw [image_univ, Subtype.range_coe]

end Langlands.Analytic.SaturatedAtlasPresentation
