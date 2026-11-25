/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Postcomposition as a linear map over the opposite endomorphism ring

In a preadditive category, `W ⟶ Y` is a module over `(End W)ᵐᵒᵖ`, acting by precomposition
(`CategoryTheory.Preadditive.moduleEndLeft`). Postcomposition with `g : Y ⟶ Z` is linear for
this action (`CategoryTheory.Preadditive.rightCompEndOp`).

In an abelian category, `Hom(W, -)` sends an exact sequence `X ⟶ Y ⟶ Z` to an exact sequence
provided `f : X ⟶ Y` has a generalized inverse `s`, with `f ≫ s ≫ f = f`
(`CategoryTheory.Preadditive.exact_rightCompEndOp_of_comp_comp_eq`).
-/

@[expose] public section

namespace CategoryTheory.Preadditive

open Limits

variable {C : Type*} [Category C]

section

variable [Preadditive C]

/-- Postcomposition with `g : Y ⟶ Z`, as a linear map `(W ⟶ Y) → (W ⟶ Z)` over `(End W)ᵐᵒᵖ`
acting by precomposition. -/
@[simps]
def rightCompEndOp (W : C) {Y Z : C} (g : Y ⟶ Z) : (W ⟶ Y) →ₗ[(End W)ᵐᵒᵖ] (W ⟶ Z) where
  toFun f := f ≫ g
  map_add' f f' := Preadditive.add_comp _ _ _ f f' g
  map_smul' r f := Category.assoc r.unop.asHom f g

end

/-- In an abelian category, if `X ⟶ Y ⟶ Z` is exact and `f : X ⟶ Y` has a generalized inverse
`s` (`f ≫ s ≫ f = f`), then `Hom(W, X) ⟶ Hom(W, Y) ⟶ Hom(W, Z)` is exact: a morphism `y` with
`y ≫ g = 0` lifts to `y ≫ s`, since `𝟙 - s ≫ f` kills the image of `f`. -/
lemma exact_rightCompEndOp_of_comp_comp_eq [Abelian C] (W : C) {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} {hfg : f ≫ g = 0} (hS : (ShortComplex.mk f g hfg).Exact) {s : Y ⟶ X}
    (hs : f ≫ s ≫ f = f) : Function.Exact (rightCompEndOp W f) (rightCompEndOp W g) := by
  intro y
  simp only [rightCompEndOp_apply, Set.mem_range]
  refine ⟨fun hy ↦ ⟨y ≫ s, ?_⟩, ?_⟩
  · obtain ⟨A', π, _, x₁, fac⟩ := hS.exact_up_to_refinements y hy
    have h : π ≫ y ≫ (𝟙 Y - s ≫ f) = 0 := by
      rw [← Category.assoc, fac, Category.assoc, Preadditive.comp_sub, Category.comp_id, hs,
        sub_self, comp_zero]
    have h' : y ≫ (𝟙 Y - s ≫ f) = 0 := by
      rw [← cancel_epi π, comp_zero]
      exact h
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h'
    rw [Category.assoc, ← h']
  · rintro ⟨x, rfl⟩
    rw [Category.assoc, hfg, comp_zero]

end CategoryTheory.Preadditive
