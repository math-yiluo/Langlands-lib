import Langlands.Geometry.Analytic.FullRecognitionQuasiIso
import Langlands.Geometry.Analytic.FullRecognitionEquivalence

/-! # Recognized category equivalence without original target closure -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {f : StrongHom A B}
  (hf : f.IsQuasiIso) (hc : f.HasCoherentPullbacks)

/-- Lift the target chart to its actual recognition iteration, use the
constructed reverse on full atlases, then flatten back to the source atlas. -/
def generalReverseRecognizedImage (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    A.atlas.saturatedAtlas.RecognizedSubset :=
  A.atlas.fullRecognitionIdempotenceIndex
    ((hf.fullRecognitionExtension_isQuasiIso hc).reverseRecognizedImage
      (hf.fullRecognitionExtension_hasCoherentPullbacks hc)
      B.fullRecognitionPresentation_hasAllLocalDomains
      (B.atlas.fullRecognitionIterationIndex W))

@[simp]
theorem generalReverseRecognizedImage_locus
    (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.generalReverseRecognizedImage hc W).locus = f.baseMap ⁻¹' W.locus := by
  change ((hf.fullRecognitionExtension_isQuasiIso hc).reverseRecognizedImage
    (hf.fullRecognitionExtension_hasCoherentPullbacks hc)
    B.fullRecognitionPresentation_hasAllLocalDomains
    (B.atlas.fullRecognitionIterationIndex W)).locus = _
  exact ((hf.fullRecognitionExtension_isQuasiIso hc).reverseRecognizedImage_locus
    (hf.fullRecognitionExtension_hasCoherentPullbacks hc)
    B.fullRecognitionPresentation_hasAllLocalDomains
    (B.atlas.fullRecognitionIterationIndex W)).trans
      (congrArg (fun S : Set B.space => f.baseMap ⁻¹' S)
        (B.atlas.fullRecognitionIterationIndex_locus W))

/-- The reverse acts on literal inclusions by the actual recognized
bounded restriction maps, with no original target closure premise. -/
def generalReverseRecognizedImageFunctor :
    B.atlas.saturatedAtlas.RecognizedSubset ⥤
      A.atlas.saturatedAtlas.RecognizedSubset where
  obj := hf.generalReverseRecognizedImage hc
  map {U V} p := ⟨by
    rw [hf.generalReverseRecognizedImage_locus, hf.generalReverseRecognizedImage_locus]
    exact Set.preimage_mono p.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem generalReverseRecognizedImage_forward_locus
    (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.generalReverseRecognizedImage hc (hf.recognizedImage hc V)).locus = V.locus := by
  rw [hf.generalReverseRecognizedImage_locus, hf.recognizedImage_locus]
  exact Set.preimage_image_eq _ hf.1.injective

theorem generalForwardRecognizedImage_reverse_locus
    (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.recognizedImage hc (hf.generalReverseRecognizedImage hc W)).locus = W.locus := by
  rw [hf.recognizedImage_locus, hf.generalReverseRecognizedImage_locus]
  exact Set.image_preimage_eq _ hf.1.surjective

/-- Literal-locus recovery gives actual inclusion isomorphisms in both
round trips; their affinoid maps remain the canonical full restrictions. -/
def generalRecognizedImageUnitComponent (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    V ≅ (hf.generalReverseRecognizedImageFunctor hc).obj
      ((hf.recognizedImageFunctor hc).obj V) where
  hom := ⟨(hf.generalReverseRecognizedImage_forward_locus hc V).symm.subset⟩
  inv := ⟨(hf.generalReverseRecognizedImage_forward_locus hc V).subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def generalRecognizedImageCounitComponent (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.recognizedImageFunctor hc).obj
      ((hf.generalReverseRecognizedImageFunctor hc).obj W) ≅ W where
  hom := ⟨(hf.generalForwardRecognizedImage_reverse_locus hc W).subset⟩
  inv := ⟨(hf.generalForwardRecognizedImage_reverse_locus hc W).symm.subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def generalRecognizedImageUnitIso :
    𝟭 A.atlas.saturatedAtlas.RecognizedSubset ≅
      hf.recognizedImageFunctor hc ⋙ hf.generalReverseRecognizedImageFunctor hc :=
  NatIso.ofComponents (hf.generalRecognizedImageUnitComponent hc) (by
    intro U V p
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

def generalRecognizedImageCounitIso :
    hf.generalReverseRecognizedImageFunctor hc ⋙ hf.recognizedImageFunctor hc ≅
      𝟭 B.atlas.saturatedAtlas.RecognizedSubset :=
  NatIso.ofComponents (hf.generalRecognizedImageCounitComponent hc) (by
    intro U V p
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

/-- The original forward image functor is an actual category equivalence
for every coherent strong quasi-isomorphism, without original atlas closure. -/
def generalRecognizedImageEquivalence :
    A.atlas.saturatedAtlas.RecognizedSubset ≌ B.atlas.saturatedAtlas.RecognizedSubset where
  functor := hf.recognizedImageFunctor hc
  inverse := hf.generalReverseRecognizedImageFunctor hc
  unitIso := hf.generalRecognizedImageUnitIso hc
  counitIso := hf.generalRecognizedImageCounitIso hc
  functor_unitIso_comp _ := @Subsingleton.elim
    (RecognizedSubset.Inclusion _ _) inferInstance _ _

include hf hc in
/-- The homeomorphism identifies the literal recognized affinoid families,
with the reverse recognized objects constructed from the original data. -/
theorem generalRecognizedAffinoidFamily_image :
    (fun S : Set A.space => f.baseMap '' S) '' A.atlas.recognizedAffinoidFamily =
      B.atlas.recognizedAffinoidFamily := by
  apply Set.Subset.antisymm
  · rintro S ⟨_, ⟨V, rfl⟩, rfl⟩
    exact ⟨hf.recognizedImage hc V, hf.recognizedImage_locus hc V⟩
  · rintro S ⟨W, rfl⟩
    refine ⟨(hf.generalReverseRecognizedImage hc W).locus, ⟨_, rfl⟩, ?_⟩
    rw [hf.generalReverseRecognizedImage_locus]
    exact Set.image_preimage_eq _ hf.1.surjective

/-- The inverse original forward comparison and constructed counit identify
the reverse actual affinoid diagrams without original closure assumptions. -/
def generalReverseRecognizedImageAffinoidNatIso :
    hf.generalReverseRecognizedImageFunctor hc ⋙
        RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace B.atlas.saturatedAtlas :=
  Functor.isoWhiskerLeft (hf.generalReverseRecognizedImageFunctor hc)
      (hf.recognizedImageAffinoidNatIso hc).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (hf.generalRecognizedImageCounitIso hc)
      (RecognizedSubset.toAffinoidSpace B.atlas.saturatedAtlas) ≪≫
    (RecognizedSubset.toAffinoidSpace B.atlas.saturatedAtlas).leftUnitor

/-- Both bounded inverses are extracted from actual affinoid morphisms;
this comparison is natural on entire bounded algebra maps. -/
def generalReverseRecognizedImageNaturalEquiv
    (V : B.atlas.saturatedAtlas.RecognizedSubset) :
    BoundedAlgEquiv K V.algebra (hf.generalReverseRecognizedImage hc V).algebra := by
  let e := (hf.generalReverseRecognizedImageAffinoidNatIso hc).app V
  exact BoundedAlgEquiv.ofHomInv (Quiver.Hom.unop e.hom) (Quiver.Hom.unop e.inv)
    (fun b => congrArg
      (fun q : Opposite.op V.algebra ⟶ Opposite.op V.algebra =>
        BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.inv_hom_id)
    (fun b => congrArg
      (fun q : Opposite.op (hf.generalReverseRecognizedImage hc V).algebra ⟶
        Opposite.op (hf.generalReverseRecognizedImage hc V).algebra =>
          BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.hom_inv_id)

theorem generalReverseRecognizedImageNaturalEquiv_naturality
    {U V : B.atlas.saturatedAtlas.RecognizedSubset} (p : U ⟶ V) :
    (hf.generalReverseRecognizedImageNaturalEquiv hc U).toBoundedAlgHom.comp p.restriction =
      ((hf.generalReverseRecognizedImageFunctor hc).map p).restriction.comp
        (hf.generalReverseRecognizedImageNaturalEquiv hc V).toBoundedAlgHom := by
  exact (congrArg
    (fun q : Opposite.op (hf.generalReverseRecognizedImage hc U).algebra ⟶
      Opposite.op V.algebra => Quiver.Hom.unop q)
    ((hf.generalReverseRecognizedImageAffinoidNatIso hc).hom.naturality p)).symm

/-- The reverse actual affinoid comparison lies over the original ambient
homeomorphism, independently of the choices in the recognition iterations. -/
theorem generalReverseRecognizedImageAffinoidNatIso_over_ambient
    (V : B.atlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (hf.generalReverseRecognizedImage hc V).algebra) :
    V.chart ((affinoidSpectrumFunctor K).map
        ((hf.generalReverseRecognizedImageAffinoidNatIso hc).hom.app V) x) =
      f.baseMap ((hf.generalReverseRecognizedImage hc V).chart x) := by
  let W := hf.generalReverseRecognizedImage hc V
  let e := hf.recognizedImageEquiv hc W
  let y := e.spectrumHomeomorph.symm x
  change V.chart ((hf.generalRecognizedImageCounitComponent hc V).hom.spectrumMap y) =
    f.baseMap (W.chart x)
  exact ((hf.generalRecognizedImageCounitComponent hc V).hom.chart_naturality y).trans
    ((hf.recognizedImage_chart hc W y).trans
      (congrArg (fun z => f.baseMap (W.chart z))
        (e.spectrumHomeomorph.apply_symm_apply x)))

theorem generalReverseRecognizedImageNaturalEquiv_chart
    (V : B.atlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (hf.generalReverseRecognizedImage hc V).algebra) :
    (hf.generalReverseRecognizedImage hc V).chart x =
      hf.inverseBaseMap
        (V.chart ((hf.generalReverseRecognizedImageNaturalEquiv hc V).spectrumHomeomorph x)) := by
  apply hf.1.injective
  rw [hf.baseMap_inverseBaseMap]
  exact (hf.generalReverseRecognizedImageAffinoidNatIso_over_ambient hc V x).symm

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso
