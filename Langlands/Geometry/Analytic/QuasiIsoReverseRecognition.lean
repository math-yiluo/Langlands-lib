import Langlands.Geometry.Analytic.QuasiIsoRecognizedImage
import Langlands.Geometry.Analytic.SubatlasRecognizedNaturality
import Langlands.Geometry.Analytic.CoherentQuasiIsoReverseSubatlas

/-! # Reverse recognized images and category equivalence with a full-domain closed target -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {f : StrongHom A B}
  (hf : f.IsQuasiIso) (hc : f.HasCoherentPullbacks)
  (hb : B.atlas.HasAllLocalDomains)

/-- The actual inverse homeomorphism sends a literal subset to its full
inverse image under the original ambient map. -/
theorem inverseBaseMap_image_eq_preimage (S : Set B.space) :
    hf.inverseBaseMap '' S = f.baseMap ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change f.baseMap (hf.inverseBaseMap y) ∈ S
    rw [hf.baseMap_inverseBaseMap]
    exact hy
  · intro hx
    exact ⟨f.baseMap x, hx, hf.inverseBaseMap_baseMap x⟩

/-- Selectively recognize W on the constructed reverse subatlas, then
take its actual recognized image under the constructed reverse quasiiso. -/
def reverseRecognizedImage (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    A.atlas.saturatedAtlas.RecognizedSubset :=
  (hf.reverseStrongMap_isQuasiIso hc hb).recognizedImage
    (hf.reverseStrongMap_hasCoherentPullbacks hc hb)
    (B.atlas.subatlasRecognizedSubset (hf.reverseChartSelection_locallyRefining hb) W)

@[simp]
theorem reverseRecognizedImage_locus (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.reverseRecognizedImage hc hb W).locus = f.baseMap ⁻¹' W.locus :=
  ((hf.reverseStrongMap_isQuasiIso hc hb).recognizedImage_locus
    (hf.reverseStrongMap_hasCoherentPullbacks hc hb)
    (B.atlas.subatlasRecognizedSubset (hf.reverseChartSelection_locallyRefining hb) W)).trans
      (hf.inverseBaseMap_image_eq_preimage W.locus)

/-- Both constituent recognition steps construct actual bounded inverse
algebra maps, and their composition recovers the original target algebra. -/
def reverseRecognizedImageEquiv (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    BoundedAlgEquiv K W.algebra (hf.reverseRecognizedImage hc hb W).algebra :=
  (B.atlas.subatlasRecognizedSubsetEquiv
    (hf.reverseChartSelection_locallyRefining hb) W).trans
      ((hf.reverseStrongMap_isQuasiIso hc hb).recognizedImageEquiv
        (hf.reverseStrongMap_hasCoherentPullbacks hc hb)
        (B.atlas.subatlasRecognizedSubset (hf.reverseChartSelection_locallyRefining hb) W))

theorem reverseRecognizedImage_chart (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (hf.reverseRecognizedImage hc hb W).algebra) :
    (hf.reverseRecognizedImage hc hb W).chart x =
      hf.inverseBaseMap
        (W.chart ((hf.reverseRecognizedImageEquiv hc hb W).spectrumHomeomorph x)) := by
  let hP := hf.reverseChartSelection_locallyRefining hb
  let S := B.atlas.subatlasRecognizedSubset hP W
  let rh := hf.reverseStrongMap_isQuasiIso hc hb
  let rc := hf.reverseStrongMap_hasCoherentPullbacks hc hb
  let e := rh.recognizedImageEquiv rc S
  exact (rh.recognizedImage_chart rc S x).trans
    (congrArg hf.inverseBaseMap
      (B.atlas.subatlasRecognizedSubset_chart hP W (e.spectrumHomeomorph x)))

/-- Forward recognized images act on all literal inclusions by the actual
recognized bounded restrictions of the target category. -/
def recognizedImageFunctor :
    A.atlas.saturatedAtlas.RecognizedSubset ⥤ B.atlas.saturatedAtlas.RecognizedSubset where
  obj := hf.recognizedImage hc
  map {U V} p := ⟨by
    rw [hf.recognizedImage_locus, hf.recognizedImage_locus]
    exact Set.image_mono p.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Reverse recognized images act by the reflected literal containments. -/
def reverseRecognizedImageFunctor :
    B.atlas.saturatedAtlas.RecognizedSubset ⥤ A.atlas.saturatedAtlas.RecognizedSubset where
  obj := hf.reverseRecognizedImage hc hb
  map {U V} p := ⟨by
    rw [hf.reverseRecognizedImage_locus, hf.reverseRecognizedImage_locus]
    exact Set.preimage_mono p.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem reverseRecognizedImage_forward_locus (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.reverseRecognizedImage hc hb (hf.recognizedImage hc V)).locus = V.locus := by
  rw [hf.reverseRecognizedImage_locus, hf.recognizedImage_locus]
  exact Set.preimage_image_eq _ hf.1.injective

theorem forwardRecognizedImage_reverse_locus (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.recognizedImage hc (hf.reverseRecognizedImage hc hb W)).locus = W.locus := by
  rw [hf.recognizedImage_locus, hf.reverseRecognizedImage_locus]
  exact Set.image_preimage_eq _ hf.1.surjective

/-- Both round trips are actual recognized inclusion isomorphisms on the
same literal subsets; their maps are the canonical bounded restrictions. -/
def recognizedImageUnitComponent (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    V ≅ (hf.reverseRecognizedImageFunctor hc hb).obj
      ((hf.recognizedImageFunctor hc).obj V) where
  hom := ⟨(hf.reverseRecognizedImage_forward_locus hc hb V).symm.subset⟩
  inv := ⟨(hf.reverseRecognizedImage_forward_locus hc hb V).subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def recognizedImageCounitComponent (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.recognizedImageFunctor hc).obj
      ((hf.reverseRecognizedImageFunctor hc hb).obj W) ≅ W where
  hom := ⟨(hf.forwardRecognizedImage_reverse_locus hc hb W).subset⟩
  inv := ⟨(hf.forwardRecognizedImage_reverse_locus hc hb W).symm.subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def recognizedImageUnitIso :
    𝟭 A.atlas.saturatedAtlas.RecognizedSubset ≅
      hf.recognizedImageFunctor hc ⋙ hf.reverseRecognizedImageFunctor hc hb :=
  NatIso.ofComponents (hf.recognizedImageUnitComponent hc hb) (by
    intro U V p
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

def recognizedImageCounitIso :
    hf.reverseRecognizedImageFunctor hc hb ⋙ hf.recognizedImageFunctor hc ≅
      𝟭 B.atlas.saturatedAtlas.RecognizedSubset :=
  NatIso.ofComponents (hf.recognizedImageCounitComponent hc hb) (by
    intro U V p
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

/-- The original input quasi-isomorphism induces an actual recognized
inclusion-category equivalence when the target is full-domain closed. -/
def recognizedImageEquivalence :
    A.atlas.saturatedAtlas.RecognizedSubset ≌ B.atlas.saturatedAtlas.RecognizedSubset where
  functor := hf.recognizedImageFunctor hc
  inverse := hf.reverseRecognizedImageFunctor hc hb
  unitIso := hf.recognizedImageUnitIso hc hb
  counitIso := hf.recognizedImageCounitIso hc hb
  functor_unitIso_comp _ := @Subsingleton.elim
    (RecognizedSubset.Inclusion _ _) inferInstance _ _

include hf hc hb in
/-- Equality of the recognized literal families under the actual ambient
homeomorphism follows from the constructed objects in both directions. -/
theorem recognizedAffinoidFamily_image :
    (fun S : Set A.space => f.baseMap '' S) '' A.atlas.recognizedAffinoidFamily =
      B.atlas.recognizedAffinoidFamily := by
  apply Set.Subset.antisymm
  · rintro S ⟨_, ⟨V, rfl⟩, rfl⟩
    exact ⟨hf.recognizedImage hc V, hf.recognizedImage_locus hc V⟩
  · rintro S ⟨W, rfl⟩
    refine ⟨(hf.reverseRecognizedImage hc hb W).locus, ⟨_, rfl⟩, ?_⟩
    rw [hf.reverseRecognizedImage_locus]
    exact Set.image_preimage_eq _ hf.1.surjective

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso
