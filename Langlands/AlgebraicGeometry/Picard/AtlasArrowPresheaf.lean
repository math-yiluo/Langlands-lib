import Langlands.AlgebraicGeometry.Picard.StackAtlas
import Langlands.AlgebraicGeometry.Picard.EtaleGroupoidClasses
import Langlands.CategoryTheory.OverTotalPresheaf

/-! # The full arrow presheaf of an actual Picard family -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))

/-- Arrows retain two actual maps to the family and their bundle isomorphism. -/
def atlasArrowPresheaf : AlgebraicSpace.Presheaf S :=
  (presheaf (relative f) (Core.mk L) (Core.mk L)).overTotal ⋙ uliftFunctor.{u + 1}

/-- The first family map of an actual arrow. -/
def atlasArrowFst :
    atlasArrowPresheaf f L ⟶ (AlgebraicSpace.schemeYoneda S).obj U where
  app _ := ↾fun x ↦ ULift.up x.down.2.1
  naturality {_ _} _ := rfl

/-- The second family map of an actual arrow. -/
def atlasArrowSnd :
    atlasArrowPresheaf f L ⟶ (AlgebraicSpace.schemeYoneda S).obj U where
  app _ := ↾fun x ↦ ULift.up x.down.1
  naturality {_ _} _ := rfl

/-- The map of a family to the unsheafified isomorphism classes. -/
def classFamilyMap :
    (AlgebraicSpace.schemeYoneda S).obj U ⟶ relativeClassPresheaf f :=
  uliftYonedaEquiv.symm (isoClass (Core.mk L))

@[simp]
lemma classFamilyMap_app {T : Over S} (a : T ⟶ U) :
    (classFamilyMap f L).app (op T) (ULift.up a) =
      isoClass ((relative f).map a.op.toLoc |>.toFunctor.obj (Core.mk L)) := rfl

/-- An actual arrow identifies the two pulled-back bundle classes. -/
lemma atlasArrow_classFamilyMap :
    atlasArrowFst f L ≫ classFamilyMap f L =
      atlasArrowSnd f L ≫ classFamilyMap f L := by
  ext T x
  exact Quotient.sound ⟨x.down.2.2⟩

/-- Equality of the unsheafified family classes is witnessed by an actual arrow. -/
lemma classFamilyMap_eq_iff {T : Over S} (a b : T ⟶ U) :
    (classFamilyMap f L).app (op T) (ULift.up a) =
        (classFamilyMap f L).app (op T) (ULift.up b) ↔
      ∃ x : (atlasArrowPresheaf f L).obj (op T),
        (atlasArrowFst f L).app (op T) x = ULift.up a ∧
          (atlasArrowSnd f L).app (op T) x = ULift.up b := by
  constructor
  · intro h
    obtain ⟨e⟩ := Quotient.exact h
    exact ⟨ULift.up ⟨b, a, e⟩, rfl, rfl⟩
  · rintro ⟨x, ha, hb⟩
    have h := congrArg (fun q ↦ q.app (op T) x) (atlasArrow_classFamilyMap f L)
    simpa only [NatTrans.comp_app, types_comp_apply, ha, hb] using h

set_option backward.isDefEq.respectTransparency false in
/-- The family class map followed by sheafification is the existing etale map. -/
lemma classFamilyMap_toEtale :
    classFamilyMap f L ≫ relativeToEtaleClassSheaf f = etaleFamilyMap f L := by
  rw [classFamilyMap, uliftYonedaEquiv_symm_comp]
  rfl

/-- The actual two family maps are equal in the full etale class sheaf. -/
lemma atlasArrow_etaleFamilyMap :
    atlasArrowFst f L ≫ etaleFamilyMap f L =
      atlasArrowSnd f L ≫ etaleFamilyMap f L := by
  rw [← classFamilyMap_toEtale]
  simpa only [← Category.assoc] using
    congrArg (fun q ↦ q ≫ relativeToEtaleClassSheaf f) (atlasArrow_classFamilyMap f L)

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
