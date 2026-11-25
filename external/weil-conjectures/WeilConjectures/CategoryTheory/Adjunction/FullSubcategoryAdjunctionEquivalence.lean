/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-! # Restriction of an adjunction to an equivalence

Source: the Restriction paragraph of the current smooth-purity tower equivalence.
(blueprint: lem-sp-full-subcategory-adjunction-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v u' v'
open CategoryTheory

namespace CategoryTheory.Adjunction

/-- An adjunction whose functors preserve full subcategories and whose unit and counit
are invertible there restricts to an equivalence with the very same unit and counit.

Source: sk-lem-sp-tower-equivalence.proof.md, Restriction paragraph
(blueprint: lem-sp-full-subcategory-adjunction-equivalence).
Proof: lift the two functors to the full subcategories. Restrict the Hom equivalence
along their fully faithful inclusions. Its unit and counit map to the ambient maps,
since the commuting squares are identity isomorphisms. Fully faithful inclusions
reflect their invertibility. Apply Adjunction.toEquivalence; its unit and counit are
the restricted adjunction maps. This also proves both functor equalities and the
asserted component equalities. -/
theorem fullSubcategoryEquivalence
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ Y : Q.FullSubcategory, P (G.obj Y.obj))
    (hη : ∀ X : P.FullSubcategory, IsIso (adj.unit.app X.obj))
    (hε : ∀ Y : Q.FullSubcategory, IsIso (adj.counit.app Y.obj)) :
    ∃ e : P.FullSubcategory ≌ Q.FullSubcategory,
      e.functor ⋙ Q.ι = P.ι ⋙ F ∧ e.inverse ⋙ P.ι = Q.ι ⋙ G ∧
      (∀ X : P.FullSubcategory, HEq (P.ι.map (e.unitIso.hom.app X))
        (adj.unit.app X.obj)) ∧
      (∀ Y : Q.FullSubcategory, HEq (Q.ι.map (e.counitIso.hom.app Y))
        (adj.counit.app Y.obj)) := by
  let L := Q.lift (P.ι ⋙ F) hF
  let R := P.lift (Q.ι ⋙ G) hG
  let a : L ⊣ R := adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  have hunit (X : P.FullSubcategory) :
      P.ι.map (a.unit.app X) = adj.unit.app X.obj := by
    simpa using
      adj.map_restrictFullyFaithful_unit_app P.fullyFaithfulι Q.fullyFaithfulι
        (show P.ι ⋙ F ≅ L ⋙ Q.ι from Iso.refl _)
        (show Q.ι ⋙ G ≅ R ⋙ P.ι from Iso.refl _) X
  have hcounit (Y : Q.FullSubcategory) :
      Q.ι.map (a.counit.app Y) = adj.counit.app Y.obj := by
    have h := adj.map_restrictFullyFaithful_counit_app P.fullyFaithfulι Q.fullyFaithfulι
      (show P.ι ⋙ F ≅ L ⋙ Q.ι from Iso.refl _)
      (show Q.ι ⋙ G ≅ R ⋙ P.ι from Iso.refl _) Y
    change Q.ι.map (a.counit.app Y) =
      𝟙 _ ≫ F.map (𝟙 _) ≫ adj.counit.app Y.obj at h
    simpa only [Functor.map_id, Category.id_comp] using h
  have hiη (X : P.FullSubcategory) : IsIso (a.unit.app X) := by
    have : IsIso (P.ι.map (a.unit.app X)) := by rw [hunit]; exact hη X
    exact isIso_of_reflects_iso _ P.ι
  have hiε (Y : Q.FullSubcategory) : IsIso (a.counit.app Y) := by
    have : IsIso (Q.ι.map (a.counit.app Y)) := by rw [hcounit]; exact hε Y
    exact isIso_of_reflects_iso _ Q.ι
  refine ⟨a.toEquivalence, rfl, rfl, ?_, ?_⟩
  · intro X
    exact heq_of_eq (hunit X)
  · intro Y
    exact heq_of_eq (hcounit Y)

end CategoryTheory.Adjunction
