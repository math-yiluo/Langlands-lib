/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!
# A generating subcategory of sheaves presents the topos

Source: Stacks Project, Sites, Tag 03A1, and Sets, Tag 000X
(blueprint: lem-weil-pbc-sheaf-subcategory-comparison).
-/

@[expose] public section

set_option linter.privateModule false
universe u v w

open CategoryTheory.Limits Opposite

namespace CategoryTheory

private noncomputable def representableLift {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) : C ⥤ E where
  obj U := (hrep U).choose
  map {U V} f := F.preimage ((hrep U).choose_spec.some.hom ≫
    (presheafToSheaf J (Type u)).map (yoneda.map f) ≫ (hrep V).choose_spec.some.inv)
  map_id U := F.map_injective (by simp)
  map_comp f g := F.map_injective (by simp)

private noncomputable def representableLiftIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) :
    representableLift F hrep ⋙ F ≅ yoneda ⋙ presheafToSheaf J (Type u) :=
  NatIso.ofComponents (fun U ↦ (hrep U).choose_spec.some) (by
    intro U V f
    dsimp [representableLift]
    simp)

private noncomputable def sectionEquiv {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (U : C) (B : Sheaf J (Type u)) :
    (F.obj ((representableLift F hrep).obj U) ⟶ B) ≃ B.obj.obj (op U) :=
  (Iso.homCongr ((representableLiftIso F hrep).app U) (Iso.refl B)).trans
    (((sheafificationAdjunction J (Type u)).homEquiv _ _).trans yonedaEquiv)

end CategoryTheory
