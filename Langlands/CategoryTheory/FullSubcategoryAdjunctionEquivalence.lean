import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Whiskering

/-! # Restricting an adjunction to the essential image of its right adjoint -/

noncomputable section

set_option maxHeartbeats 800000

universe uC uD vC vD

open CategoryTheory

namespace Langlands.Renard

/-- If a full faithful right adjoint has precisely a full subcategory as its
essential image, the restricted left adjoint is an equivalence. Its unit is
also an isomorphism in the ambient category. -/
theorem fullSubcategory_adjunction_equivalence
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (Q : ObjectProperty C) (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    [R.Full] [R.Faithful]
    (hR : ∀ X, Q (R.obj X))
    (hess : ∀ Y : Q.FullSubcategory, ∃ X, Nonempty (R.obj X ≅ Y.obj)) :
    (Q.ι ⋙ L).Faithful ∧
      (∀ Y : Q.FullSubcategory, IsIso (adj.unit.app Y.obj)) ∧
      ∃ E : Q.FullSubcategory ≌ D, E.functor = Q.ι ⋙ L ∧
        Nonempty (E.inverse ⋙ Q.ι ≅ R) := by
  let I : D ⥤ Q.FullSubcategory := Q.lift R hR
  have : I.Full := inferInstanceAs (Q.lift R hR).Full
  have : I.Faithful := inferInstanceAs (Q.lift R hR).Faithful
  have : I.EssSurj := ⟨fun Y => by
    obtain ⟨X, ⟨e⟩⟩ := hess Y
    exact ⟨X, ⟨Q.isoMk e⟩⟩⟩
  have : I.IsEquivalence := {}
  let adj' : (Q.ι ⋙ L) ⊣ I :=
    adj.restrictFullyFaithful (iC := Q.ι) (iD := 𝟭 D) (L := Q.ι ⋙ L) (R := I)
      Q.fullyFaithfulι (Functor.FullyFaithful.id D)
      (Iso.refl _) (Iso.refl _)
  have : (Q.ι ⋙ L).IsEquivalence := adj'.isEquivalence_left_of_isEquivalence_right
  refine ⟨inferInstance, ?_, ?_⟩
  · intro Y
    have hunit : Q.ι.map (adj'.unit.app Y) = adj.unit.app Y.obj := by
      simpa using
        adj.map_restrictFullyFaithful_unit_app (iC := Q.ι) (iD := 𝟭 D)
          (L := Q.ι ⋙ L) (R := I) Q.fullyFaithfulι
          (Functor.FullyFaithful.id D) (Iso.refl _) (Iso.refl _) Y
    rw [← hunit]
    infer_instance
  · let E := (Q.ι ⋙ L).asEquivalence
    refine ⟨E, rfl, ⟨?_⟩⟩
    exact Functor.isoWhiskerRight (E.toAdjunction.rightAdjointUniq adj') Q.ι ≪≫
      Q.liftCompιIso R hR

set_option linter.defProp false in
/-- The restricted-adjunction equivalence result as a defined proof term. -/
def fullSubcategoryAdjunctionEquivalence :=
  @fullSubcategory_adjunction_equivalence

end Langlands.Renard
