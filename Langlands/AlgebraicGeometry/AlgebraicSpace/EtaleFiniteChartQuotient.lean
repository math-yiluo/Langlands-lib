import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof

/-! # Affine open images of charts with finite kernel pair -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F : Presheaf S} {U : Over S}

/-- A scheme chart has a represented kernel pair with finite projections. -/
def HasFiniteKernelPair (a : (schemeYoneda S).obj U ⟶ F) : Prop :=
  ∃ (R : Over S) (t s : R ⟶ U),
    IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a ∧
      _root_.AlgebraicGeometry.IsFinite t.left ∧
      _root_.AlgebraicGeometry.IsFinite s.left

/-- The image of an affine etale chart with finite kernel pair in an fppf
sheaf is an affine open subfunctor. -/
theorem isAffineOpen_sheafify_range_of_hasFiniteKernelPair [IsAffine U.left]
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a)
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F)
    (hfin : HasFiniteKernelPair a) :
    AffineOpenSubfunctors.IsAffineOpen
      ((Subfunctor.range a).sheafify (fppfTopology S)) := by
  obtain ⟨R, t, s, h, htfin, hsfin⟩ := hfin
  let Q := (Subfunctor.range a).sheafify (fppfTopology S)
  let Y : FppfSheaf S := ⟨Q.toFunctor,
    OpenSubfunctorImages.sheafify_range_isSheaf a ha hF⟩
  let b : (schemeYoneda S).obj U ⟶ Y.obj :=
    Subfunctor.toRangeSheafify (fppfTopology S) a
  have hb : b ≫ Q.ι = a := by ext T x; rfl
  have h' : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) b b := by
    apply IsKernelPair.cancel_right_of_mono (f₂ := Q.ι)
    rwa [hb]
  have ht : Etale t.left := ha.projection a _ _ h.flip
  have hs : Etale s.left := ha.projection a _ _ h
  let : Etale t.left := ht
  let : Etale s.left := hs
  let E := EtaleEquivalenceRelation.ofKernelPair t s b h' ht hs
  obtain ⟨M, q, hM, hq, _, hflat, hlfp, hsurj⟩ :=
    finiteLocallyFreeEquivalenceRelationAffineQuotient E.U E.R E.t E.s
      E.mono_lift E.refl E.symm E.trans htfin
      (inferInstanceAs (Flat t.left)) (inferInstanceAs (LocallyOfFinitePresentation t.left))
      hsfin (inferInstanceAs (Flat s.left))
      (inferInstanceAs (LocallyOfFinitePresentation s.left)) (inferInstanceAs (IsAffine U.left))
  have hquot : E.HasAffineQuotient := ⟨M, q, hM, hq, hflat, hlfp, hsurj⟩
  exact ⟨OpenSubfunctorImages.sheafify_range_open a ha,
    EtaleEquivalenceRelation.exists_isAffine_iso_of_hasAffineQuotient h' ht hs
      (OpenSubfunctorImages.toRangeSheafify_isEtale a ha)
      (OpenSubfunctorImages.toRangeSheafify_isSurjective a ha) hquot⟩

/-- A finite scheme composite through a monomorphism supplies the finite
kernel pair of the original chart. -/
theorem hasFiniteKernelPair_of_finite_mono_composite {T : Over S}
    (a : (schemeYoneda S).obj U ⟶ F)
    (f : F ⟶ (schemeYoneda S).obj T) [Mono f] (w : U ⟶ T)
    (hw : a ≫ f = (schemeYoneda S).map w)
    [_root_.AlgebraicGeometry.IsFinite w.left] :
    HasFiniteKernelPair a := by
  let h := IsPullback.of_hasPullback w w
  have h' := h.map (schemeYoneda S)
  rw [← hw] at h'
  refine ⟨Limits.pullback w w, pullback.fst w w, pullback.snd w w,
    IsKernelPair.cancel_right_of_mono h', ?_, ?_⟩
  · exact MorphismProperty.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsFinite.{u}) (h.map (Over.forget S)).flip
      (inferInstanceAs (_root_.AlgebraicGeometry.IsFinite w.left))
  · exact MorphismProperty.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsFinite.{u}) (h.map (Over.forget S))
      (inferInstanceAs (_root_.AlgebraicGeometry.IsFinite w.left))

/-- An affine etale chart whose composite through a monomorphism is finite
has affine open image. -/
theorem isAffineOpen_sheafify_range_of_finite_mono_composite [IsAffine U.left]
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a)
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F)
    {T : Over S} (f : F ⟶ (schemeYoneda S).obj T) [Mono f] (w : U ⟶ T)
    (hw : a ≫ f = (schemeYoneda S).map w)
    [_root_.AlgebraicGeometry.IsFinite w.left] :
    AffineOpenSubfunctors.IsAffineOpen
      ((Subfunctor.range a).sheafify (fppfTopology S)) :=
  isAffineOpen_sheafify_range_of_hasFiniteKernelPair a ha hF
    (hasFiniteKernelPair_of_finite_mono_composite a f w hw)

end Langlands.AlgebraicGeometry.AlgebraicSpace
