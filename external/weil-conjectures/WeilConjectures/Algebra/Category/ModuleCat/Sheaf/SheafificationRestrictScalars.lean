/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Sheafification commutes with restriction of scalars

For a morphism `α : A ⟶ B` of sheaves of rings and a presheaf of `B`-modules `P`, the
sheafification of the restriction of scalars of `P` is the restriction of scalars of the
sheafification of `P` (`SheafOfModules.sheafificationRestrictScalarsIso`): on underlying
abelian sheaves the comparison map is the identity.
Source: Stacks Project, Tag 03CZ.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b r

open CategoryTheory

namespace SheafOfModules

variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]


/-- Sheafification commutes with restriction of scalars: the comparison map.
Source: Stacks Project, Tag 03CZ. -/
noncomputable def sheafificationRestrictScalarsHom
    {A B : Sheaf J RingCat.{r}} (α : A ⟶ B) (P : PresheafOfModules.{r} B.obj) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
    (SheafOfModules.restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 A.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P))

/-- On underlying abelian sheaves the comparison map is the identity. -/
theorem toSheaf_map_sheafificationRestrictScalarsHom
    {A B : Sheaf J RingCat.{r}} (α : A ⟶ B) (P : PresheafOfModules.{r} B.obj) :
    (SheafOfModules.toSheaf A).map (SheafOfModules.sheafificationRestrictScalarsHom α P) =
      𝟙 ((PresheafOfModules.toPresheaf B.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj P) := by
  rw [SheafOfModules.sheafificationRestrictScalarsHom,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  rfl

/-- Sheafification commutes with restriction of scalars.
Source: Stacks Project, Tag 03CZ. -/
noncomputable def sheafificationRestrictScalarsIso
    {A B : Sheaf J RingCat.{r}} (α : A ⟶ B) (P : PresheafOfModules.{r} B.obj) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ≅
    (SheafOfModules.restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B.obj)).obj P) :=
  have : IsIso (SheafOfModules.sheafificationRestrictScalarsHom α P) := by
    have : IsIso ((SheafOfModules.toSheaf A).map
        (SheafOfModules.sheafificationRestrictScalarsHom α P)) := by
      rw [SheafOfModules.toSheaf_map_sheafificationRestrictScalarsHom]
      exact IsIso.id _
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf A)
  asIso (SheafOfModules.sheafificationRestrictScalarsHom α P)

/-- Naturality of the sheafification and restriction comparison. -/
theorem sheafificationRestrictScalarsIso_hom_naturality
    {A B : Sheaf J RingCat.{r}} (α : A ⟶ B)
    {P Q : PresheafOfModules.{r} B.obj} (φ : P ⟶ Q) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).map
        ((PresheafOfModules.restrictScalars α.hom).map φ) ≫
      (SheafOfModules.sheafificationRestrictScalarsIso α Q).hom =
    (SheafOfModules.sheafificationRestrictScalarsIso α P).hom ≫
      (SheafOfModules.restrictScalars α).map
        ((PresheafOfModules.sheafification (𝟙 B.obj)).map φ) := by
  apply (SheafOfModules.toSheaf A).map_injective
  simp only [Functor.map_comp]
  change _ ≫ (SheafOfModules.toSheaf A).map
      (SheafOfModules.sheafificationRestrictScalarsHom α Q) =
    (SheafOfModules.toSheaf A).map (SheafOfModules.sheafificationRestrictScalarsHom α P) ≫ _
  rw [SheafOfModules.toSheaf_map_sheafificationRestrictScalarsHom,
    SheafOfModules.toSheaf_map_sheafificationRestrictScalarsHom]
  change (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf B.obj).map φ) ≫ 𝟙 _ =
    𝟙 _ ≫ (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf B.obj).map φ)
  simp only [Category.comp_id, Category.id_comp]

end SheafOfModules
