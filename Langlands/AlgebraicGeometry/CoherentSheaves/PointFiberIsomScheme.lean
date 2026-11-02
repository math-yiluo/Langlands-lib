import Langlands.AlgebraicGeometry.CoherentSheaves.ProperIsomRepresentabilityStatement
import Langlands.AlgebraicGeometry.Stacks.PointFiberRepresentability

/-! # Actual coherent-family point fibres from product-base Isom schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Langlands.CategoryTheory

variable {S X : Scheme.{u}} (f : X ⟶ S) {U T : Over S}

private instance liftedIsGroupoid (A : Over S) :
    IsGroupoid ((PseudofunctorHomLift.homLift.{u + 1} (pseudofunctor f)).obj (.mk (op A))) := by
  change IsGroupoid (ULiftHom.{u + 1} (FamilyGroupoid f A))
  exact isGroupoid_of_reflects_iso (ULiftHom.equiv (C := FamilyGroupoid f A)).inverse

variable (M : FamilyGroupoid f U) (N : FamilyGroupoid f T)

/-- The product Hom presheaf is the actual coherent-family Isom presheaf
of the two projection pullbacks, with exactly the specified hom lift. -/
def productIsomComparison :
    Stacks.productHomPresheaf (PseudofunctorHomLift.homLift.{u + 1} (pseudofunctor f))
      (ULiftHom.objUp.{u + 1, u + 1} M) (ULiftHom.objUp.{u + 1, u + 1} N) ≅
    isomPresheaf f ((pullback f (prod.fst : U ⨯ T ⟶ U)).obj M)
      ((pullback f (prod.snd : U ⨯ T ⟶ T)).obj N) :=
  Iso.refl _

variable {I : Over (U ⨯ T).left}
  (e : (AlgebraicSpace.schemeYoneda (U ⨯ T).left).obj I ≅
    isomPresheaf f ((pullback f (prod.fst : U ⨯ T ⟶ U)).obj M)
      ((pullback f (prod.snd : U ⨯ T ⟶ T)).obj N))

/-- A supplied actual product-base Isom scheme represents the entire coherent
point fibre over the test scheme, naturally on all schemes in its slice. -/
def pointFiberIsomSchemeIso :
    (AlgebraicSpace.schemeYoneda T.left).obj (Stacks.pointFiberScheme I) ≅
      Stacks.pointFiberPresheaf (PseudofunctorHomLift.homLift.{u + 1} (pseudofunctor f))
        (ULiftHom.objUp.{u + 1, u + 1} M) (ULiftHom.objUp.{u + 1, u + 1} N) :=
  Stacks.pointFiberSchemeIso _ _ _ (e ≪≫ (productIsomComparison f M N).symm)

/-- Conditional consequence of the exact proper Isom theorem: every actual
point fibre has a scheme representative factoring through an affine locally
finitely presented map to the product base. -/
lemma exists_pointFiberIsomScheme_of_properIsom
    (h : ProperIsomRepresentabilityStatement.{u})
    (hf : IsProper f) (hfp : LocallyOfFinitePresentation f) :
    ∃ I : Over (U ⨯ T).left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj (Stacks.pointFiberScheme I) ≅
        Stacks.pointFiberPresheaf (PseudofunctorHomLift.homLift.{u + 1} (pseudofunctor f))
          (ULiftHom.objUp.{u + 1, u + 1} M) (ULiftHom.objUp.{u + 1, u + 1} N)) ∧
      IsAffineHom I.hom ∧ LocallyOfFinitePresentation I.hom := by
  obtain ⟨I, ⟨e⟩, hI, hIfp⟩ := h S X f hf hfp (U ⨯ T)
    ((pullback f (prod.fst : U ⨯ T ⟶ U)).obj M)
    ((pullback f (prod.snd : U ⨯ T ⟶ T)).obj N)
  exact ⟨I, ⟨pointFiberIsomSchemeIso f M N e⟩, hI, hIfp⟩

end Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid
