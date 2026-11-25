/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Whiskering

/-!
# Lax and oplax monoidal functors: the tensorator as a natural transformation

Supplement to `Mathlib.CategoryTheory.Monoidal.Functor`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.
The dual `Functor.OplaxMonoidal.δNatTrans` for oplax monoidal functors is added here.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category _root_.CategoryTheory.Functor MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

namespace Functor

namespace LaxMonoidal

section

variable (F : C ⥤ D) [F.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- The tensorator on a lax monoidal functor `F : C ⥤ D`,
as a natural transformation between bifunctors in `C ⥤ C ⥤ D`. -/
@[simps!]
noncomputable def μNatTrans :
    (((whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) ⟶
      (Functor.postcompose₂.obj F).obj (curriedTensor C) where
  app X₁ := { app X₂ := μ F X₁ X₂ }

end

end LaxMonoidal

namespace OplaxMonoidal

variable (F : C ⥤ D) [F.OplaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- The comonoidal structure `δ F X Y : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y` of an oplax
monoidal functor `F : C ⥤ D`, as a natural transformation between bifunctors in `C ⥤ C ⥤ D`.
This is the dual of `Functor.LaxMonoidal.μNatTrans`; for a strong monoidal functor, the
uncurried version is `Functor.Monoidal.μNatIso`. -/
@[simps!]
noncomputable def δNatTrans :
    (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) where
  app X₁ := { app X₂ := δ F X₁ X₂ }

instance [∀ X Y, IsIso (δ F X Y)] (X Y : C) : IsIso (((δNatTrans F).app X).app Y) :=
  inferInstanceAs (IsIso (δ F X Y))

instance [∀ X Y, IsIso (δ F X Y)] (X : C) : IsIso ((δNatTrans F).app X) :=
  NatIso.isIso_of_isIso_app _

instance [∀ X Y, IsIso (δ F X Y)] : IsIso (δNatTrans F) :=
  NatIso.isIso_of_isIso_app _

end OplaxMonoidal

namespace LaxMonoidal

/-- Transport a lax monoidal structure along an isomorphism of functors. -/
@[implicit_reducible]
def ofIso {F G : C ⥤ D} [F.LaxMonoidal] (e : F ≅ G) : G.LaxMonoidal where
  ε := ε F ≫ e.hom.app _
  μ X Y := (e.inv.app X ⊗ₘ e.inv.app Y) ≫ μ F X Y ≫ e.hom.app _
  μ_natural_left {X₁ Y₁} f₁ X₂ := by
    rw [Category.assoc, Category.assoc, ← e.hom.naturality,
      ← μ_natural_left_assoc, tensorHom_def_assoc,
      ← comp_whiskerRight_assoc, e.inv.naturality,
      tensorHom_def'_assoc, ← comp_whiskerRight_assoc, whisker_exchange_assoc]
  μ_natural_right X₂ {Y₂ X₁} f₂ := by
    rw [Category.assoc, Category.assoc, ← e.hom.naturality,
      ← μ_natural_right_assoc, tensorHom_def'_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, e.inv.naturality,
      tensorHom_def_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      whisker_exchange_assoc]
  associativity X₁ X₂ X₃ := by
    have := associativity F X₁ X₂ X₃
    rw [assoc, assoc, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
      tensorHom_def'_assoc, ← whisker_exchange_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, ← comp_whiskerRight_assoc (e.hom.app _),
      Iso.hom_inv_id_app, id_whiskerRight, id_comp, ← e.hom.naturality,
      associativity_assoc, tensor_whiskerLeft_assoc,
      tensorHom_def' (e.inv.app X₂),
      MonoidalCategory.whiskerLeft_comp_assoc,
      tensorHom_def, comp_whiskerRight_assoc, whisker_assoc,
      assoc, assoc, Iso.inv_hom_id_assoc,
      associator_naturality_left_assoc, Iso.inv_hom_id_assoc,
      ← whisker_exchange_assoc, ← whisker_exchange_assoc,
      tensorHom_def'_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc _ (e.hom.app _),
      Iso.hom_inv_id_app, MonoidalCategory.whiskerLeft_id, id_comp]
  left_unitality X := by
    rw [assoc, assoc, tensorHom_def_assoc,
      ← comp_whiskerRight_assoc, assoc, e.hom_inv_id_app, comp_id,
      ← whisker_exchange_assoc, id_whiskerLeft_assoc, left_unitality_inv_assoc,
      NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_map, comp_id]
  right_unitality X := by
    rw [assoc, assoc, tensorHom_def'_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      assoc, Iso.hom_inv_id_app, comp_id, whisker_exchange_assoc,
      MonoidalCategory.whiskerRight_id_assoc, right_unitality_inv_assoc,
      NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_map, comp_id]

end LaxMonoidal

end Functor

end CategoryTheory
