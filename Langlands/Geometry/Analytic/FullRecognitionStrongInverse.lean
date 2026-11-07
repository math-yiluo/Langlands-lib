import Langlands.Geometry.Analytic.GeneralQuasiIsoRecognition
import Langlands.Geometry.Analytic.SaturatedStrongQuasiIsomorphisms

/-! # Actual inverse strong maps on full recognition atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace SaturatedAtlasPresentation

/-- The full-recognition construction is an actual object of the category
whose morphisms retain every admissible bounded pullback. -/
def ofFullRecognition (A : AffinoidAtlasPresentation.{u, v, w} K) :
    SaturatedAtlasPresentation.{u, v, v} K where
  presentation := A.fullRecognitionPresentation
  hasAllLocalDomains := A.fullRecognitionPresentation_hasAllLocalDomains

end SaturatedAtlasPresentation

namespace AffinoidAtlasPresentation.StrongHom.IsQuasiIso

variable {A B : AffinoidAtlasPresentation.{u, v, w} K} {f : StrongHom A B}
  (hf : f.IsQuasiIso) (hc : f.HasCoherentPullbacks)

theorem generalReverseRecognizedImage_locus_eq_inverse_image
    (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.generalReverseRecognizedImage hc W).locus = hf.inverseBaseMap '' W.locus := by
  rw [hf.generalReverseRecognizedImage_locus]
  ext x
  constructor
  · intro hx
    exact ⟨f.baseMap x, hx, hf.inverseBaseMap_baseMap x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [Set.mem_preimage, hf.baseMap_inverseBaseMap] using hy

theorem generalReverseRecognizedImage_subset_of_image_subset
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : hf.inverseBaseMap '' W.locus ⊆ V.locus) :
    (hf.generalReverseRecognizedImage hc W).locus ⊆ V.locus := by
  rw [hf.generalReverseRecognizedImage_locus_eq_inverse_image]
  exact h

/-- Every reverse-admissible pair has an actual bounded pullback, using
the canonical source restriction and inverse reverse-diagram comparison. -/
def fullRecognitionReversePullback
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : hf.inverseBaseMap '' W.locus ⊆ V.locus) :
    BoundedAlgHom K V.algebra W.algebra :=
  (hf.generalReverseRecognizedImageNaturalEquiv hc W).symm.toBoundedAlgHom.comp
    ((hf.generalReverseRecognizedImage hc W).restriction V
      (hf.generalReverseRecognizedImage_subset_of_image_subset hc W V h))

theorem fullRecognitionReversePullback_chart
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : hf.inverseBaseMap '' W.locus ⊆ V.locus)
    (x : BanachSpectrum W.algebra) :
    V.chart (BanachSpectrum.comap
      (hf.fullRecognitionReversePullback hc W V h).toBoundedRingHom x) =
        hf.inverseBaseMap (W.chart x) := by
  let e := hf.generalReverseRecognizedImageNaturalEquiv hc W
  let Y := hf.generalReverseRecognizedImage hc W
  let r := Y.restriction V
    (hf.generalReverseRecognizedImage_subset_of_image_subset hc W V h)
  have hp : BanachSpectrum.comap
      (hf.fullRecognitionReversePullback hc W V h).toBoundedRingHom x =
      BanachSpectrum.comap r.toBoundedRingHom (e.spectrumHomeomorph.symm x) :=
    BanachSpectrum.ext fun _ => rfl
  exact (congrArg V.chart hp).trans
    ((Y.chart_restriction V _ (e.spectrumHomeomorph.symm x)).trans
      ((hf.generalReverseRecognizedImageNaturalEquiv_chart hc W
        (e.spectrumHomeomorph.symm x)).trans
          (congrArg (fun y => hf.inverseBaseMap (W.chart y))
            (e.spectrumHomeomorph.apply_symm_apply x))))

set_option maxRecDepth 2000 in
/-- Naturality of the constructed reverse affinoid diagram proves equality
of the entire reverse bounded maps in both chart variables. -/
theorem fullRecognitionReversePullback_naturality
    (U W : B.atlas.saturatedAtlas.RecognizedSubset)
    (V Z : A.atlas.saturatedAtlas.RecognizedSubset)
    (hUW : U.locus ⊆ W.locus) (hVZ : V.locus ⊆ Z.locus)
    (hUV : hf.inverseBaseMap '' U.locus ⊆ V.locus)
    (hWZ : hf.inverseBaseMap '' W.locus ⊆ Z.locus) :
    (U.restriction W hUW).comp (hf.fullRecognitionReversePullback hc W Z hWZ) =
      (hf.fullRecognitionReversePullback hc U V hUV).comp (V.restriction Z hVZ) := by
  let Y := hf.generalReverseRecognizedImage hc U
  let T := hf.generalReverseRecognizedImage hc W
  let e := hf.generalReverseRecognizedImageNaturalEquiv hc U
  let d := hf.generalReverseRecognizedImageNaturalEquiv hc W
  have hYT : Y.locus ⊆ T.locus := by
    rw [hf.generalReverseRecognizedImage_locus, hf.generalReverseRecognizedImage_locus]
    exact Set.preimage_mono hUW
  let hYV := hf.generalReverseRecognizedImage_subset_of_image_subset hc U V hUV
  let hTZ := hf.generalReverseRecognizedImage_subset_of_image_subset hc W Z hWZ
  have hn := hf.generalReverseRecognizedImageNaturalEquiv_naturality hc
    (show U ⟶ W from ⟨hUW⟩)
  ext x
  apply e.injective
  have h₁ := congrArg (fun q : BoundedAlgHom K W.algebra Y.algebra =>
    q (d.symm (T.restriction Z hTZ x))) hn
  have h₂ := congrArg (fun q : BoundedAlgHom K Z.algebra Y.algebra => q x)
    (Y.restriction_comp T Z hYT hTZ)
  have h₃ := congrArg (fun q : BoundedAlgHom K Z.algebra Y.algebra => q x)
    (Y.restriction_comp V Z hYV hVZ)
  change e (U.restriction W hUW (d.symm (T.restriction Z hTZ x))) =
    e (e.symm (Y.restriction V hYV (V.restriction Z hVZ x)))
  rw [e.apply_symm_apply]
  exact h₁.trans ((congrArg (Y.restriction T hYT)
    (d.apply_symm_apply (T.restriction Z hTZ x))).trans (h₂.trans h₃.symm))

/-- The complete affinoid-domain universal property is transported through
the constructed bounded equivalence, for every coefficient test. -/
theorem fullRecognitionReversePullback_represents
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : hf.inverseBaseMap '' W.locus ⊆ V.locus) :
    Represents K (hf.fullRecognitionReversePullback hc W V h)
      (V.chart ⁻¹' (hf.inverseBaseMap '' W.locus)) := by
  have hr := ((hf.generalReverseRecognizedImage hc W).restriction_represents V
    (hf.generalReverseRecognizedImage_subset_of_image_subset hc W V h)).postcomp_equiv
      (hf.generalReverseRecognizedImageNaturalEquiv hc W).symm
  rw [hf.generalReverseRecognizedImage_locus_eq_inverse_image] at hr
  exact hr

/-- An actual reverse strong map on the entire target full atlas.
No selection of target charts or original closure premise is needed. -/
def fullRecognitionReverse :
    StrongHom B.fullRecognitionPresentation A.fullRecognitionPresentation where
  baseMap := hf.inverseBaseMap
  target_exists W := by
    change B.atlas.saturatedAtlas.RecognizedSubset at W
    refine ⟨hf.generalReverseRecognizedImage hc W, ?_⟩
    change hf.inverseBaseMap '' Set.range W.chart ⊆
      Set.range (hf.generalReverseRecognizedImage hc W).chart
    rw [W.range_chart, (hf.generalReverseRecognizedImage hc W).range_chart,
      hf.generalReverseRecognizedImage_locus_eq_inverse_image]
  pullback W V h := hf.fullRecognitionReversePullback hc W V (by
    change B.atlas.saturatedAtlas.RecognizedSubset at W
    change A.atlas.saturatedAtlas.RecognizedSubset at V
    change hf.inverseBaseMap '' Set.range W.chart ⊆ Set.range V.chart at h
    simpa only [W.range_chart, V.range_chart] using h)
  chart_comm W V h x := hf.fullRecognitionReversePullback_chart hc W V _ x
  restriction_comm U W V Z hUW hVZ hUV hWZ := by
    change B.atlas.saturatedAtlas.RecognizedSubset at U W
    change A.atlas.saturatedAtlas.RecognizedSubset at V Z
    change Set.range U.chart ⊆ Set.range W.chart at hUW
    change Set.range V.chart ⊆ Set.range Z.chart at hVZ
    exact hf.fullRecognitionReversePullback_naturality hc U W V Z
      (by simpa only [U.range_chart, W.range_chart] using hUW)
      (by simpa only [V.range_chart, Z.range_chart] using hVZ) _ _

@[simp]
theorem fullRecognitionReverse_baseMap :
    (hf.fullRecognitionReverse hc).baseMap = hf.inverseBaseMap := rfl

theorem fullRecognitionReverse_isQuasiIso :
    (hf.fullRecognitionReverse hc).IsQuasiIso := by
  refine ⟨hf.1.homeomorph.symm.isHomeomorph, ?_⟩
  intro W V h
  change B.atlas.saturatedAtlas.RecognizedSubset at W
  change A.atlas.saturatedAtlas.RecognizedSubset at V
  change hf.inverseBaseMap '' Set.range W.chart ⊆ Set.range V.chart at h
  have hlocus : hf.inverseBaseMap '' W.locus ⊆ V.locus := by
    simpa only [W.range_chart, V.range_chart] using h
  change Represents K (hf.fullRecognitionReversePullback hc W V hlocus)
    (V.chart ⁻¹' (hf.inverseBaseMap '' Set.range W.chart))
  rw [W.range_chart]
  exact hf.fullRecognitionReversePullback_represents hc W V _

theorem fullRecognitionReverse_hasCoherentPullbacks :
    (hf.fullRecognitionReverse hc).HasCoherentPullbacks :=
  (hf.fullRecognitionReverse hc).hasCoherentPullbacks_of_saturated
    B.fullRecognitionPresentation_hasAllLocalDomains

set_option maxRecDepth 2000 in
/-- The forward map at the reverse recognized chart is precisely the
bounded counit comparison used to construct the reverse map. -/
theorem fullRecognitionPullback_generalReverse
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' (hf.generalReverseRecognizedImage hc W).locus ⊆ W.locus) :
    hf.fullRecognitionPullback hc (hf.generalReverseRecognizedImage hc W) W h =
      (hf.generalReverseRecognizedImageNaturalEquiv hc W).toBoundedAlgHom := by
  rfl

set_option maxRecDepth 2000 in
/-- At its own reverse recognized image, the reverse bounded pullback is
the inverse comparison, as an equality of complete bounded maps. -/
theorem fullRecognitionReversePullback_generalReverse
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : hf.inverseBaseMap '' W.locus ⊆
      (hf.generalReverseRecognizedImage hc W).locus) :
    hf.fullRecognitionReversePullback hc W (hf.generalReverseRecognizedImage hc W) h =
      (hf.generalReverseRecognizedImageNaturalEquiv hc W).symm.toBoundedAlgHom := by
  change (hf.generalReverseRecognizedImageNaturalEquiv hc W).symm.toBoundedAlgHom.comp
    ((hf.generalReverseRecognizedImage hc W).restriction
      (hf.generalReverseRecognizedImage hc W) _) = _
  rw [RecognizedSubset.restriction_self, BoundedAlgHom.comp_id]

set_option maxRecDepth 2000 in
/-- The reverse followed by the original extension is the entire strong
identity, retaining bounded pullbacks on every admissible pair. -/
theorem fullRecognitionReverse_comp_extension :
    (hf.fullRecognitionReverse hc).saturatedComp (hf.fullRecognitionExtension hc)
      B.fullRecognitionPresentation_hasAllLocalDomains
      A.fullRecognitionPresentation_hasAllLocalDomains =
        StrongHom.id B.fullRecognitionPresentation := by
  have hbase :
      ((hf.fullRecognitionReverse hc).saturatedComp (hf.fullRecognitionExtension hc)
        B.fullRecognitionPresentation_hasAllLocalDomains
        A.fullRecognitionPresentation_hasAllLocalDomains).baseMap =
          (StrongHom.id B.fullRecognitionPresentation).baseMap := by
    ext x
    exact hf.baseMap_inverseBaseMap x
  refine StrongHom.ext_of_saturated
    B.fullRecognitionPresentation_hasAllLocalDomains hbase ?_
  intro W
  change B.atlas.saturatedAtlas.RecognizedSubset at W
  let V := hf.generalReverseRecognizedImage hc W
  have hR : (hf.fullRecognitionReverse hc).baseMap '' Set.range W.chart ⊆
      Set.range V.chart := by
    change hf.inverseBaseMap '' Set.range W.chart ⊆ Set.range V.chart
    rw [W.range_chart, V.range_chart,
      hf.generalReverseRecognizedImage_locus_eq_inverse_image]
  have hE : (hf.fullRecognitionExtension hc).baseMap '' Set.range V.chart ⊆
      Set.range W.chart := by
    change f.baseMap '' Set.range V.chart ⊆ Set.range W.chart
    rw [V.range_chart, W.range_chart, hf.generalReverseRecognizedImage_locus]
    exact (Set.image_preimage_eq _ hf.1.surjective).subset
  have h := (hf.fullRecognitionReverse hc).comp_admissible
    (hf.fullRecognitionExtension hc) W V W hR hE
  refine ⟨W, h, ?_⟩
  rw [StrongHom.saturatedComp_pullback (hf.fullRecognitionReverse hc)
    (hf.fullRecognitionExtension hc)
    B.fullRecognitionPresentation_hasAllLocalDomains
    A.fullRecognitionPresentation_hasAllLocalDomains W V W hR hE h]
  have hRl : hf.inverseBaseMap '' W.locus ⊆ V.locus := by
    exact ((Set.image_mono W.range_chart.symm.subset).trans hR).trans V.range_chart.subset
  have hEl : f.baseMap '' V.locus ⊆ W.locus := by
    exact ((Set.image_mono V.range_chart.symm.subset).trans hE).trans W.range_chart.subset
  change (hf.fullRecognitionReversePullback hc W V hRl).comp
    (hf.fullRecognitionPullback hc V W hEl) = W.restriction W Subset.rfl
  rw [hf.fullRecognitionPullback_generalReverse hc W,
    hf.fullRecognitionReversePullback_generalReverse hc W, W.restriction_self]
  ext x
  exact (hf.generalReverseRecognizedImageNaturalEquiv hc W).symm_apply_apply x

set_option maxRecDepth 2000 in
/-- Cancellation by the forward full quasi-isomorphism recovers the other
entire strong identity. -/
theorem fullRecognitionExtension_comp_reverse :
    (hf.fullRecognitionExtension hc).saturatedComp (hf.fullRecognitionReverse hc)
      A.fullRecognitionPresentation_hasAllLocalDomains
      B.fullRecognitionPresentation_hasAllLocalDomains =
        StrongHom.id A.fullRecognitionPresentation := by
  apply (hf.fullRecognitionExtension_isQuasiIso hc).cancel_saturatedComp
    A.fullRecognitionPresentation_hasAllLocalDomains
    A.fullRecognitionPresentation_hasAllLocalDomains
  rw [StrongHom.saturatedComp_assoc,
    hf.fullRecognitionReverse_comp_extension hc,
    StrongHom.saturatedComp_id, StrongHom.id_saturatedComp]

/-- An actual categorical isomorphism between the full recognition atlases,
with the original extension and the constructed all-pair reverse as its maps. -/
def fullRecognitionStrongIso :
    SaturatedAtlasPresentation.ofFullRecognition A ≅
      SaturatedAtlasPresentation.ofFullRecognition B where
  hom := hf.fullRecognitionExtension hc
  inv := hf.fullRecognitionReverse hc
  hom_inv_id := hf.fullRecognitionExtension_comp_reverse hc
  inv_hom_id := hf.fullRecognitionReverse_comp_extension hc

end AffinoidAtlasPresentation.StrongHom.IsQuasiIso
end Langlands.Analytic
