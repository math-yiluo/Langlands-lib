/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.NatIso

/-!
# Invertibility of a natural transformation at an object is invariant under isomorphism

This file records the observation that whether a natural transformation is invertible at an
object only depends on the isomorphism class of that object. It is the form in which
`AlgebraicGeometry.Etale.isIso_app_of_isIso_openImmersionRestriction` transports invertibility
of a morphism of sheaves from an étale `U`-scheme to an isomorphic étale `X`-scheme.

## Main results

- `CategoryTheory.NatTrans.isIso_app_of_iso`, and its version
  `CategoryTheory.NatTrans.isIso_app_app_of_iso` for bifunctors.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]

/-- Invertibility of a natural transformation at an object only depends on the object up to
isomorphism. -/
lemma NatTrans.isIso_app_of_iso {F G : C ⥤ A} (φ : F ⟶ G) {X Y : C} (e : X ≅ Y)
    [IsIso (φ.app Y)] : IsIso (φ.app X) := by
  have key : φ.app X = F.map e.hom ≫ φ.app Y ≫ inv (G.map e.hom) := by
    rw [← Category.assoc, φ.naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [key]
  infer_instance

/-- Conjugating the image of a morphism under a functor `F₁` by isomorphisms is the same as
conjugating its image under an isomorphic functor `F₂`. -/
lemma conj_eq_comp_conj {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} (c : F₁ ≅ F₂) {X Y : C} (φ : X ⟶ Y) {A B A' B' : D}
    (t₁ : F₁.obj X ≅ A) (s₁ : F₁.obj Y ≅ B) (t₂ : F₂.obj X ≅ A') (s₂ : F₂.obj Y ≅ B') :
    t₁.inv ≫ F₁.map φ ≫ s₁.hom =
      (t₁.symm ≪≫ c.app X ≪≫ t₂).hom ≫ (t₂.inv ≫ F₂.map φ ≫ s₂.hom) ≫
        (s₂.symm ≪≫ (c.app Y).symm ≪≫ s₁).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.hom_inv_id_assoc, NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc]

/-- Conjugating the image of a morphism under a functor `F₁` by isomorphisms is the same as
conjugating its image under an isomorphic functor `F₂` by the composite isomorphisms. -/
lemma conj_eq_comp_conj' {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} (c : F₁ ≅ F₂) {X Y : C} (φ : X ⟶ Y) {A B : D}
    (t₁ : F₁.obj X ≅ A) (s₁ : F₁.obj Y ≅ B) :
    t₁.inv ≫ F₁.map φ ≫ s₁.hom =
      (t₁.symm ≪≫ c.app X).hom ≫ F₂.map φ ≫ ((c.app Y).symm ≪≫ s₁).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc]

/-- A component `(τ.app M').app L'` of a natural transformation of bifunctors is an isomorphism
if the component at isomorphic arguments `(M, L)` is. -/
lemma NatTrans.isIso_app_app_of_iso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D ⥤ E} (τ : F ⟶ G) {M M' : C} {L L' : D}
    (eM : M ≅ M') (eL : L ≅ L') [IsIso ((τ.app M).app L)] : IsIso ((τ.app M').app L') := by
  have h₁ := (τ.app M).naturality eL.hom
  have h₂ := congr_app (τ.naturality eM.hom) L'
  dsimp at h₂
  have : IsIso ((F.obj M).map eL.hom ≫ (τ.app M).app L') := by
    rw [h₁]
    infer_instance
  have : IsIso ((τ.app M).app L') := IsIso.of_isIso_comp_left ((F.obj M).map eL.hom) _
  have : IsIso ((F.map eM.hom).app L' ≫ (τ.app M').app L') := by
    rw [h₂]
    infer_instance
  exact IsIso.of_isIso_comp_left ((F.map eM.hom).app L') _

end CategoryTheory
