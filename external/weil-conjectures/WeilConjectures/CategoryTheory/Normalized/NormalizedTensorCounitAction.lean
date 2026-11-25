/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Tensor linearity forced by a normalized trace counit -/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory MonoidalCategory
namespace CategoryTheory

/-- A counit normalized by a trace respects the coefficient action.
Source: the coefficient-action calculation in the affine-space trace proof,
Stacks Tags 0B56 and 0GL1
(blueprint: lem-pur-normalized-tensor-counit-action).

Proof: precompose by the invertible map `H tensor p B W`. The action equation
replaces the two projections by the projection for `H tensor B` and its
associator. The inverse associator and inverse tensorator then cancel. Apply
normalization at `H tensor B` and at `B`. Naturality of the associator moves
the trace to the last factor, and the right-unitor coherence finishes. -/
theorem normalizedTensorCounit_action
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (G : D ⥤ C)
    (p : ∀ (K : C) (M : D), K ⊗ G.obj M ⟶ G.obj (F.obj K ⊗ M))
    [∀ K M, IsIso (p K M)]
    (hp : ∀ (H B : C) (M : D),
      p (H ⊗ B) M ≫ G.map (Functor.OplaxMonoidal.δ F H B ▷ M ≫
        (α_ (F.obj H) (F.obj B) M).hom) =
      (α_ H B (G.obj M)).hom ≫ H ◁ p B M ≫ p H (F.obj B ⊗ M))
    (W : D) (b : G.obj W ⟶ 𝟙_ C)
    (c : ∀ K : C, G.obj (F.obj K ⊗ W) ⟶ K)
    (hc : ∀ K : C, p K W ≫ c K = K ◁ b ≫ (ρ_ K).hom)
    (H B : C) :
    p H (F.obj B ⊗ W) ≫
      G.map ((α_ (F.obj H) (F.obj B) W).inv ≫
        Functor.LaxMonoidal.μ F H B ▷ W) ≫ c (H ⊗ B) = H ◁ c B := by
  apply (cancel_epi (H ◁ p B W)).mp
  have ha := congrArg (fun z ↦ (α_ H B (G.obj W)).inv ≫ z) (hp H B W)
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at ha
  rw [← reassoc_of% ha]
  have hcancel :
      G.map (Functor.OplaxMonoidal.δ F H B ▷ W ≫
        (α_ (F.obj H) (F.obj B) W).hom) ≫
      G.map ((α_ (F.obj H) (F.obj B) W).inv ≫
        Functor.LaxMonoidal.μ F H B ▷ W) = 𝟙 _ := by
    rw [← G.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight,
      Functor.Monoidal.δ_μ, id_whiskerRight, G.map_id]
  rw [← Category.assoc (G.map _) (G.map _), hcancel, Category.id_comp, hc]
  rw [← whiskerLeft_comp, hc]
  rw [whiskerLeft_comp]
  rw [← associator_inv_naturality_right_assoc]
  rw [← whiskerLeft_rightUnitor H B]

end CategoryTheory
