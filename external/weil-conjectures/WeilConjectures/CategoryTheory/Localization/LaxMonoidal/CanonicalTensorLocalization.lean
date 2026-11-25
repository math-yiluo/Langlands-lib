/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-!
# Lax monoidal descent along a strong monoidal localization

The tensorator of a lax monoidal functor descends as a natural transformation,
without an invertibility assumption. This adapts Mathlib's strong monoidal descent
proof, retaining the same coherence argument and recording the unit and tensor
normalizations for the specified lifting isomorphism.

Source: the canonical evaluation pairing in blueprint local boundary duality,
Step 5, and Mathlib's `CategoryTheory.Localization.Monoidal.Functor`.
(blueprint: lem-a1-canonical-lax-localization)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory

open CategoryTheory MonoidalCategory CategoryTheory.Functor MonoidalCategory.Functor Monoidal
open LaxMonoidal OplaxMonoidal

namespace Localization.LaxMonoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Monoidal]
  (F : D ⥤ E) (G : C ⥤ E) [G.LaxMonoidal] [W.ContainsIdentities] [Lifting L W G F]

@[simps]
instance lifting₂CurriedTensorPreLax :
    Lifting₂ L L W W (curriedTensorPre G) (curriedTensorPre F) where
  iso := curriedTensorPreFunctor.mapIso (Lifting.iso L W G F)

@[simps]
instance lifting₂CurriedTensorPostLax :
    Lifting₂ L L W W (curriedTensorPost G) (curriedTensorPost F) where
  iso := (postcompose₂.obj F).mapIso (curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)

/--
The tensor natural transformation descended from the lax tensorator of `G`.
-/
noncomputable def laxTensor : curriedTensorPre F ⟶ curriedTensorPost F :=
  lift₂NatTrans L L W W (curriedTensorPre G) (curriedTensorPost G) _ _
    { app X := { app Y := μ G X Y
                 naturality := fun _ _ f => by exact μ_natural_right G X f }
      naturality := fun _ _ f => by
        ext Y
        exact μ_natural_left G f Y }

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma laxTensor_app_app (X₁ X₂ : C) :
    letI e := Lifting.iso L W G F
    ((laxTensor L W F G).app (L.obj X₁)).app (L.obj X₂) =
      (e.hom.app _ ⊗ₘ e.hom.app _) ≫ LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _) := by
  simp [laxTensor]

set_option backward.defeqAttrib.useBackward true in
lemma laxTensor_app_app' {X₁ X₂ : C} {Y₁ Y₂ : D}
    (e₁ : Y₁ ≅ L.obj X₁) (e₂ : Y₂ ≅ L.obj X₂) :
    letI e := Lifting.iso L W G F
    ((laxTensor L W F G).app Y₁).app Y₂ =
      ((F.map e₁.hom ≫ e.hom.app _) ⊗ₘ (F.map e₂.hom ≫ e.hom.app _)) ≫
        LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _ ≫ (e₁.inv ⊗ₘ e₂.inv)) := by
  have h₁ := ((laxTensor L W F G).app Y₁).naturality e₂.hom
  have h₂ := congr_app ((laxTensor L W F G).naturality e₁.hom)
  dsimp at h₁ h₂ ⊢
  rw [← cancel_mono (F.map (Y₁ ◁ e₂.hom)), ← h₁,
    ← cancel_mono (F.map (e₁.hom ▷ L.obj X₂)),
    Category.assoc, ← h₂, laxTensor_app_app, Category.assoc, Category.assoc,
    Category.assoc, Category.assoc, ← tensorHom_def'_assoc, tensorHom_comp_tensorHom_assoc,
    ← Functor.map_comp, ← tensorHom_def', ← Functor.map_comp, Category.assoc,
    tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, tensorHom_id, id_whiskerRight,
    Category.comp_id]

/-- Descend a lax structure along `L`, normalized by the specified lifting isomorphism.

Proof: lift the curried tensor natural transformation in both variables and transport
its unit by the lifting isomorphism. Localization extensionality reduces all three
coherence diagrams to those of `G` and `L`. Only the tensorators of `L` are inverted.
Source: blueprint local boundary duality, Step 5; Mathlib's strong descent argument.
(blueprint: lem-a1-canonical-lax-localization) -/
@[simps!, instance_reducible]
noncomputable def functorLaxMonoidalOfComp : F.LaxMonoidal := by
  letI e := Lifting.iso L W G F
  refine Functor.LaxMonoidal.ofBifunctor
    (ε G ≫ e.inv.app _ ≫ F.map (η L)) (laxTensor L W F G) ?_ ?_ ?_
  · refine natTrans₃_ext L L L W W W (fun X₁ X₂ X₃ ↦ ?_)
    dsimp [e]
    rw [laxTensor_app_app, laxTensor_app_app,
      laxTensor_app_app' L W F G (μIso L _ _) (Iso.refl _),
      laxTensor_app_app' L W F G (Iso.refl _) (μIso L _ _)]
    monoidal_simps
    -- The following `simp only` block is the suggestion of `simp` with the arguments
    -- `[← comp_whiskerRight_assoc, -comp_whiskerRight, whisker_exchange_assoc,
    --   ← MonoidalCategory.whiskerLeft_comp_assoc, -MonoidalCategory.whiskerLeft_comp]`.
    simp only [comp_obj, μIso_hom, Iso.refl_hom, map_id, Category.id_comp, μIso_inv, Iso.refl_inv,
      MonoidalCategory.whiskerLeft_id, Category.comp_id, map_comp, Category.assoc,
      ← comp_whiskerRight_assoc, δ_μ_map_assoc, Iso.inv_hom_id_app, id_whiskerRight,
      whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, whiskerRight_tensor]
    simp [← whisker_exchange_assoc, tensor_whiskerLeft_symm, -tensor_whiskerLeft,
      ← LaxMonoidal.associativity_assoc G, ← Functor.map_comp]
  · refine natTrans_ext L W (fun X₂ ↦ ?_)
    have := NatTrans.congr_app ((laxTensor L W F G).naturality (εIso L).inv)
      (L.obj X₂)
    dsimp [e] at this ⊢
    monoidal_simps
    simp [reassoc_of% this, laxTensor_app_app, ← comp_whiskerRight_assoc,
      -comp_whiskerRight, tensorHom_def, ← whisker_exchange_assoc, ← map_comp]
  · refine natTrans_ext L W (fun X₁ ↦ ?_)
    have := ((laxTensor L W F G).app (L.obj X₁)).naturality (εIso L).inv
    dsimp [e] at this ⊢
    monoidal_simps
    simp [reassoc_of% this, laxTensor_app_app, tensorHom_def,
      whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ← map_comp]

lemma functorLaxMonoidalOfComp_tensor (X Y : C) :
    (functorLaxMonoidalOfComp L W F G).μ (L.obj X) (L.obj Y) ≫
      F.map (LaxMonoidal.μ L X Y) ≫ (Lifting.iso L W G F).hom.app (X ⊗ Y) =
    ((Lifting.iso L W G F).hom.app X ⊗ₘ (Lifting.iso L W G F).hom.app Y) ≫
      LaxMonoidal.μ G X Y := by
  change ((laxTensor L W F G).app (L.obj X)).app (L.obj Y) ≫ _ ≫ _ = _
  rw [laxTensor_app_app]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, Monoidal.δ_μ, F.map_id, Category.id_comp,
    Iso.inv_hom_id_app, Category.comp_id]

lemma functorLaxMonoidalOfComp_unit :
    (functorLaxMonoidalOfComp L W F G).ε ≫ F.map (LaxMonoidal.ε L) ≫
      (Lifting.iso L W G F).hom.app (𝟙_ C) = LaxMonoidal.ε G := by
  change (LaxMonoidal.ε G ≫ (Lifting.iso L W G F).inv.app _ ≫
    F.map (OplaxMonoidal.η L)) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, Monoidal.η_ε, F.map_id, Category.id_comp,
    Iso.inv_hom_id_app, Category.comp_id]

end CategoryTheory.Localization.LaxMonoidal
