import Langlands.Geometry.Analytic.FullRecognitionEtaleComposition
import Langlands.Geometry.Analytic.FullRecognitionStrongInverse
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion
import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods
import Langlands.Geometry.Analytic.CompatibleStrongQuasiIsomorphisms

/-! # Finite étaleness of full quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {f : StrongHom A B}
  (hf : f.IsQuasiIso) (hc : f.HasCoherentPullbacks)

/-- The actual enlarged pullback on a chart and its entire image is the
inverse of the constructed bounded image comparison. -/
theorem saturationExtension_pullback_saturatedImage
    (s : A.atlas.saturatedAtlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.saturatedAtlas.chart s) ⊆
      Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s))) :
    (f.saturationExtension hc).pullback s (hf.saturatedImageIndex s) h =
      (hf.saturatedImageEquiv s).symm.toBoundedAlgHom := by
  let U := A.atlas.saturatedRepresentative s
  let D := hf.domainImage U
  let V := B.atlas.saturatedRepresentative (hf.saturatedImageIndex s)
  let e := LocalDomain.isoOfLocusEq D V
    (B.atlas.saturatedRepresentative_locus (hf.saturatedImageIndex s)).symm
  have hUV : f.baseMap '' U.locus ⊆ V.locus := by
    rw [← U.range_ambientMap, ← V.range_ambientMap]
    exact h
  change f.localDomainPullback U V hUV = e.hom.restriction
  symm
  apply f.localDomainPullback_unique
  have hD : D.locus ⊆ Set.range (B.atlas.chart V.index) :=
    e.hom.subset.trans
      (B.atlas.domainSubset_chart V.index V.index V.domain V.domain Subset.rfl)
  have hV : V.locus ⊆ Set.range (B.atlas.chart V.index) :=
    B.atlas.domainSubset_chart V.index V.index V.domain V.domain Subset.rfl
  have he := e.hom.comp_chart V.index hD hV
  rw [B.atlas.domainChartRestriction_self V.index V.domain hV] at he
  exact he.trans (hf.domainImage_chartRestriction U V.index hD _)

/-- Descent to a recognized chart and its entire image retains the actual
inverse image-algebra comparison. -/
theorem saturationExtension_fullRecognitionPairs_pullback_recognizedImage
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' Set.range V.chart ⊆
      Set.range (hf.recognizedImage hc V).chart) :
    (f.saturationExtension hc).fullRecognitionPairs.pullback
      V (hf.recognizedImage hc V) h =
        (hf.recognizedImageEquiv hc V).symm.toBoundedAlgHom := by
  apply V.hom_ext
  intro s hs
  have hST : f.baseMap '' Set.range (A.atlas.saturatedAtlas.chart s) ⊆
      Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s)) :=
    (hf.saturatedImage_range s).symm.subset
  rw [(f.saturationExtension hc).originalRestriction_comp_fullRecognitionPairs
    V (hf.recognizedImage hc V) h s hs (hf.saturatedImageIndex s)
      (hf.saturatedImage_subset_recognizedImage hc V s hs) hST,
    hf.saturationExtension_pullback_saturatedImage hc s hST]
  apply BoundedAlgHom.ext
  intro x
  apply (hf.saturatedImageEquiv s).injective
  have hn := congrArg
    (fun q : BoundedAlgHom K V.algebra
      (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)) =>
        q ((hf.recognizedImageEquiv hc V).symm x))
    (hf.recognizedImageEquiv_originalRestriction hc V s hs)
  change (hf.saturatedImageEquiv s)
      ((hf.saturatedImageEquiv s).symm
        ((hf.recognizedImage hc V).originalRestriction (hf.saturatedImageIndex s)
          (hf.saturatedImage_subset_recognizedImage hc V s hs) x)) =
    (hf.saturatedImageEquiv s)
      (V.originalRestriction s hs ((hf.recognizedImageEquiv hc V).symm x))
  rw [(hf.saturatedImageEquiv s).apply_symm_apply]
  simpa only [recognitionImageChartDomain, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply,
    BoundedAlgEquiv.apply_symm_apply] using hn

/-- The pair-system extension is the constructed quasi-isomorphism extension
on every recognized pair, as equality of complete bounded maps. -/
theorem saturationExtension_fullRecognitionPairs_pullback
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (hl : f.baseMap '' V.locus ⊆ W.locus) :
    (f.saturationExtension hc).fullRecognitionPairs.pullback V W h =
      hf.fullRecognitionPullback hc V W hl := by
  have hY : f.baseMap '' Set.range V.chart ⊆
      Set.range (hf.recognizedImage hc V).chart := by
    rw [V.range_chart, (hf.recognizedImage hc V).range_chart,
      hf.recognizedImage_locus]
  have hYW : Set.range (hf.recognizedImage hc V).chart ⊆ Set.range W.chart := by
    rw [(hf.recognizedImage hc V).range_chart, W.range_chart]
    exact hf.recognizedImage_subset_of_image_subset hc V W hl
  have hr := (f.saturationExtension hc).fullRecognitionPairs.restriction_comm
    V V (hf.recognizedImage hc V) W Set.Subset.rfl hYW hY h
  rw [A.fullRecognitionPresentation.atlas.restriction_id V Set.Subset.rfl,
    BoundedAlgHom.id_comp,
    hf.saturationExtension_fullRecognitionPairs_pullback_recognizedImage hc V hY] at hr
  exact hr

include hf in
/-- The actual pair-system map of the local-domain extension represents its
literal relative image over every recognized target chart. -/
theorem saturationExtension_fullRecognitionPairs_represents
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (hl : f.baseMap '' V.locus ⊆ W.locus) :
    Represents K ((f.saturationExtension hc).fullRecognitionPairs.pullback V W h)
      (W.chart ⁻¹' (f.baseMap '' V.locus)) := by
  rw [hf.saturationExtension_fullRecognitionPairs_pullback hc V W h hl]
  exact hf.fullRecognitionPullback_represents hc V W hl

/-- A full-image recognized pair has its actual bounded pullback as the
forward map of a bounded algebra equivalence. -/
def saturationExtension_fullRecognitionPairEquiv
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (hl : f.baseMap '' V.locus ⊆ W.locus)
    (hu : W.chart ⁻¹' (f.baseMap '' V.locus) = Set.univ) :
    BoundedAlgEquiv K W.algebra V.algebra :=
  ((congrArg (fun s => Represents K
    ((f.saturationExtension hc).fullRecognitionPairs.pullback V W h) s) hu).mp
      (hf.saturationExtension_fullRecognitionPairs_represents hc V W h hl)).univEquiv

/-- The equivalence preserves the complete actual bounded map. -/
theorem saturationExtension_fullRecognitionPairEquiv_toBoundedAlgHom
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (hl : f.baseMap '' V.locus ⊆ W.locus)
    (hu : W.chart ⁻¹' (f.baseMap '' V.locus) = Set.univ) :
    (hf.saturationExtension_fullRecognitionPairEquiv hc V W h hl hu).toBoundedAlgHom =
      (f.saturationExtension hc).fullRecognitionPairs.pullback V W h :=
  Represents.univEquiv_toBoundedAlgHom _

include hf in
/-- A coherent quasi-isomorphism becomes finite étale on its actual
local-domain enlargements. -/
theorem saturationExtension_isFiniteEtale :
    (f.saturationExtension hc).IsFiniteEtale := by
  refine ⟨Set.subset_univ _, fun W _ => ?_⟩
  let V := hf.generalReverseRecognizedImage hc W
  have hl : f.baseMap '' V.locus ⊆ W.locus := by
    rw [hf.generalReverseRecognizedImage_locus]
    exact Set.image_preimage_subset _ _
  have h : f.baseMap '' Set.range V.chart ⊆ Set.range W.chart := by
    rw [V.range_chart, W.range_chart]
    exact hl
  refine ⟨V, h, ?_, ?_⟩
  · rw [Set.univ_inter]
    exact hf.generalReverseRecognizedImage_locus hc W
  · have heq : W.chart ⁻¹' (f.baseMap '' V.locus) = Set.univ := by
      rw [hf.generalReverseRecognizedImage_locus,
        Set.image_preimage_eq _ hf.1.surjective, ← W.range_chart]
      exact Set.preimage_range _
    let e := hf.saturationExtension_fullRecognitionPairEquiv hc V W h hl heq
    constructor
    · obtain ⟨M, hM, hb⟩ := e.symm.bounded
      refine BoundedAlgHom.isFiniteBanach_of_lift _ hM fun z => ?_
      exact ⟨e.symm z, e.apply_symm_apply z, hb z⟩
    · exact BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _
        e.toAlgEquiv.bijective

include hf in
/-- The denominator's actual enlarged representative is étale over all
recognized affinoid pieces. -/
theorem saturationExtension_isEtaleAllPieces :
    (f.saturationExtension hc).IsEtaleAllPieces :=
  (hf.saturationExtension_isFiniteEtale hc).isEtaleAllPieces

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso
