import Langlands.AlgebraicGeometry.Picard.ProperLineBundleIsomRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.StackAtlasComparison
import Langlands.AlgebraicGeometry.Stacks.PointFiberRepresentability
import Langlands.CategoryTheory.Sites.PseudofunctorHomLiftHomPresheaf

/-! # Actual Picard point fibres from product-base Isom schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Langlands.CategoryTheory

variable {S X : Scheme.{u}} (f : X ⟶ S) {U T : Over S}

private instance relativeHomLiftIsGroupoid (A : Over S) :
    IsGroupoid ((relativeHomLift f).obj (.mk (op A))) := by
  change IsGroupoid (ULiftHom.{u + 1} (PicardGroupoid ((relativeSpace f).obj A)))
  exact isGroupoid_of_reflects_iso
    (ULiftHom.equiv (C := PicardGroupoid ((relativeSpace f).obj A))).inverse

variable (L : LineBundle ((relativeSpace f).obj U))
  (M : LineBundle ((relativeSpace f).obj T))

/-- The product Hom presheaf of the lifted actual Picard pseudofunctor
is the direct Isom presheaf of the two projection pullbacks. -/
def productIsomComparison :
    Stacks.productHomPresheaf (relativeHomLift f)
      (ULiftHom.objUp.{u + 1, u + 1} (Core.mk L))
      (ULiftHom.objUp.{u + 1, u + 1} (Core.mk M)) ≅
    relativeIsomPresheaf f
      (((relative f).map (prod.fst : U ⨯ T ⟶ U).op.toLoc).toFunctor.obj (Core.mk L))
      (((relative f).map (prod.snd : U ⨯ T ⟶ T).op.toLoc).toFunctor.obj (Core.mk M)) :=
  Functor.isoWhiskerLeft (U ⨯ T).iteratedSliceBackward.op
      (PseudofunctorHomLift.presheafHomIso.{u + 1} (relative f)
        (((relative f).map (prod.fst : U ⨯ T ⟶ U).op.toLoc).toFunctor.obj (Core.mk L))
        (((relative f).map (prod.snd : U ⨯ T ⟶ T).op.toLoc).toFunctor.obj (Core.mk M))) ≪≫
    (Functor.associator _ _ _).symm

variable {I : Over (U ⨯ T).left}
  (e : (AlgebraicSpace.schemeYoneda (U ⨯ T).left).obj I ≅
    relativeIsomPresheaf f
      (((relative f).map (prod.fst : U ⨯ T ⟶ U).op.toLoc).toFunctor.obj (Core.mk L))
      (((relative f).map (prod.snd : U ⨯ T ⟶ T).op.toLoc).toFunctor.obj (Core.mk M)))

/-- A supplied product-base Isom scheme represents the entire actual concrete
Picard point fibre on all schemes over the test scheme. -/
def pointFiberIsomSchemeIso :
    (AlgebraicSpace.schemeYoneda T.left).obj (Stacks.pointFiberScheme I) ≅
      pointFiberPresheaf f L M :=
  Stacks.pointFiberSchemeIso _ _ _ (e ≪≫ (productIsomComparison f L M).symm) ≪≫
    pointFiberPresheafHomLiftIso f L M

/-- Conditional consequence of the focused line-bundle Isom theorem,
retaining the affine locally finitely presented map to the product base. -/
lemma exists_pointFiberIsomScheme_of_properLineBundleIsom
    (h : ProperLineBundleIsomRepresentabilityStatement.{u})
    (hf : IsProper f) (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) :
    ∃ I : Over (U ⨯ T).left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj (Stacks.pointFiberScheme I) ≅
        pointFiberPresheaf f L M) ∧
      IsAffineHom I.hom ∧ LocallyOfFinitePresentation I.hom := by
  obtain ⟨I, ⟨e⟩, hI, hIfp⟩ := h S X f hf hflat hfp (U ⨯ T)
    (((relative f).map (prod.fst : U ⨯ T ⟶ U).op.toLoc).toFunctor.obj (Core.mk L))
    (((relative f).map (prod.snd : U ⨯ T ⟶ T).op.toLoc).toFunctor.obj (Core.mk M))
  exact ⟨I, ⟨pointFiberIsomSchemeIso f L M e⟩, hI, hIfp⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
