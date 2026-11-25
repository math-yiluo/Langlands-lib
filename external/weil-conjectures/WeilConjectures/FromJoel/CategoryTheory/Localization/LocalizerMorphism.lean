/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Localizer morphisms: localized equivalences and opposites

Supplement to `Mathlib.CategoryTheory.Localization.LocalizerMorphism`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Localization _root_.CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)

/-- The property of functors `C₁ ⥤ C₂` of sending morphisms in `W₁` to
morphisms in `W₂`. -/
def ObjectProperty.localizerMorphism :
    ObjectProperty (C₁ ⥤ C₂) := fun F ↦ W₁ ≤ W₂.inverseImage F

variable {W₁ W₂ W₃} in
lemma ObjectProperty.localizerMorphism.comp {F : C₁ ⥤ C₂}
    (h : localizerMorphism W₁ W₂ F) {G : C₂ ⥤ C₃} (h' : localizerMorphism W₂ W₃ G) :
    localizerMorphism W₁ W₃ (F ⋙ G) :=
  fun _ _ _ hf ↦ h' _ (h _ hf)

set_option backward.defeqAttrib.useBackward true in
instance [W₂.RespectsIso] :
    (ObjectProperty.localizerMorphism W₁ W₂).IsClosedUnderIsomorphisms where
  of_iso e h _ _ f hf :=
    (W₂.arrow_mk_iso_iff (Arrow.isoMk (e.app _) (e.app _))).1 (h _ hf)

namespace LocalizerMorphism

variable {W₁ W₂ W₃} (Φ : LocalizerMorphism W₁ W₂)

lemma isLocalizedEquivalence_op_iff :
    Φ.op.IsLocalizedEquivalence ↔ Φ.IsLocalizedEquivalence := by
  constructor
  · intro
    have hG : (Φ.op.localizedFunctor W₁.Q.op W₂.Q.op).IsEquivalence := inferInstance
    let _ : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op (Φ.op.localizedFunctor W₁.Q.op W₂.Q.op) :=
      LocalizerMorphism.catCommSq _ _ _
    let _ : CatCommSq Φ.functor W₁.Q W₂.Q (Φ.op.localizedFunctor W₁.Q.op W₂.Q.op).unop :=
      ⟨NatIso.unop (F := W₁.Q.op ⋙ Φ.op.localizedFunctor W₁.Q.op W₂.Q.op)
        (G := Φ.op.functor ⋙ W₂.Q.op)
        (CatCommSq.iso Φ.op.functor W₁.Q.op W₂.Q.op
          (Φ.op.localizedFunctor W₁.Q.op W₂.Q.op)).symm⟩
    have : (Φ.op.localizedFunctor W₁.Q.op W₂.Q.op).unop.IsEquivalence :=
      ((Φ.op.localizedFunctor W₁.Q.op W₂.Q.op).asEquivalence.unop).isEquivalence_functor
    exact IsLocalizedEquivalence.mk' Φ W₁.Q W₂.Q
      (Φ.op.localizedFunctor W₁.Q.op W₂.Q.op).unop
  · intro
    infer_instance

variable {Φ} in
lemma isLocalizedEquivalence_of_iso {Φ' : LocalizerMorphism W₁ W₂} (e : Φ.functor ≅ Φ'.functor)
    [Φ.IsLocalizedEquivalence] : Φ'.IsLocalizedEquivalence := by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  have : CatCommSq Φ'.functor W₁.Q W₂.Q G :=
    ⟨isoWhiskerRight e.symm _ ≪≫ CatCommSq.iso Φ.functor W₁.Q W₂.Q G⟩
  exact IsLocalizedEquivalence.mk' Φ' W₁.Q W₂.Q G

lemma isLocalizedEquivalence_of_precomp (Ψ : LocalizerMorphism W₂ W₃)
    [Φ.IsLocalizedEquivalence] [(Φ.comp Ψ).IsLocalizedEquivalence] :
    Ψ.IsLocalizedEquivalence := by
  let G₁₂ := Φ.localizedFunctor W₁.Q W₂.Q
  let G₂₃ := Ψ.localizedFunctor W₂.Q W₃.Q
  have : CatCommSq (Φ.comp Ψ).functor W₁.Q W₃.Q (G₁₂ ⋙ G₂₃) :=
    ⟨Functor.associator _ _ _ ≪≫ isoWhiskerLeft _
        (CatCommSq.iso Ψ.functor W₂.Q W₃.Q (Ψ.localizedFunctor W₂.Q W₃.Q)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (CatCommSq.iso Φ.functor W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)) _ ≪≫
      Functor.associator _ _ _⟩
  have := isEquivalence (Φ.comp Ψ) W₁.Q W₃.Q (G₁₂ ⋙ G₂₃)
  have := Functor.isEquivalence_of_comp_left G₁₂ G₂₃
  exact IsLocalizedEquivalence.mk' Ψ W₂.Q W₃.Q G₂₃


end LocalizerMorphism

end CategoryTheory
