/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Deriving functors using a derivability structure (supplement)

Supplement to `Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives`,
migrated from the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

When `h : Φ.Derives F` holds and `Φ` is a left derivability structure,
we show that `F` has a left derived functor with respect to `W₂`.
Under this assumption, if `L₂ : C₂ ⥤ D₂` is a localization functor
for `W₂`, then a functor `LF : D₂ ⥤ H` equipped with a natural
transformation `α : L₂ ⋙ LF ⟶ F` is the left derived functor of `F` iff
for any `X₁ : C₁`, the map `α.app (Φ.functor.obj X₁)` is an isomorphism.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Limits Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₂ : Type u₄} [Category.{v₄} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable {Φ : LocalizerMorphism W₁ W₂} {F : C₂ ⥤ H} (h : Φ.Derives F)

namespace Derives

set_option backward.defeqAttrib.useBackward true in
include h in
protected lemma op : Φ.op.Derives F.op := fun _ _ f hf ↦ by
  have := h f.unop hf
  dsimp at this ⊢
  infer_instance

include h in
lemma hasLeftDerivedFunctor [Φ.IsLeftDerivabilityStructure] :
    F.HasLeftDerivedFunctor W₂ := by
  rw [Functor.hasLeftDerivedFunctor_iff_op]
  have := h.op.hasPointwiseRightDerivedFunctor
  infer_instance

section

variable {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {RF : D₂ ⥤ H} (α : F ⟶ L₂ ⋙ RF)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma of_isIso_app_functor_obj (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    Φ.Derives F := by
  intro X₁ X₂ f hf
  have := Localization.inverts L₂ W₂ _ (Φ.map f hf)
  rw [Functor.comp_map, ← isIso_comp_right_iff _ (α.app _), α.naturality (Φ.functor.map f),
    isIso_comp_left_iff, Functor.comp_map]
  infer_instance

end

section

variable {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {LF : D₂ ⥤ H} (α : L₂ ⋙ LF ⟶ F)

include h in
lemma isIso_of_isLeftDerivedFunctor
    [Φ.IsLeftDerivabilityStructure] (X₁ : C₁) [LF.IsLeftDerivedFunctor α W₂] :
    IsIso (α.app (Φ.functor.obj X₁)) := by
  have := h.op.isIso_of_isRightDerivedFunctor (RF := LF.op) (F := F.op)
    (L₂ := L₂.op) (NatTrans.op α) (Opposite.op X₁)
  rwa [← isIso_unop_iff] at this

set_option backward.isDefEq.respectTransparency false in
lemma of_isIso_app_functor_obj' (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    Φ.Derives F := by
  intro X₁ X₂ f hf
  have := Localization.inverts L₂ W₂ _ (Φ.map f hf)
  rw [Functor.comp_map, ← isIso_comp_left_iff (α.app _),
    ← α.naturality (Φ.functor.map f), isIso_comp_right_iff, Functor.comp_map]
  infer_instance

end

end Derives

variable (Φ) in
lemma isRightDerivedFunctor_of_isRightDerivabilityStructure
    [Φ.IsRightDerivabilityStructure]
    {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {RF : D₂ ⥤ H}
    (α : F ⟶ L₂ ⋙ RF) (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    RF.IsRightDerivedFunctor α W₂ :=
  (Derives.of_isIso_app_functor_obj α hα).isRightDerivedFunctor_of_isIso _ hα

variable (Φ) in
lemma isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    [Φ.IsLeftDerivabilityStructure]
    {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {LF : D₂ ⥤ H}
    (α : L₂ ⋙ LF ⟶ F) (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    LF.IsLeftDerivedFunctor α W₂ :=
  (Derives.of_isIso_app_functor_obj' α hα).isLeftDerivedFunctor_of_isIso _ hα

end LocalizerMorphism

end CategoryTheory
