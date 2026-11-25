/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Monoidal functors preserve exact pairings

A monoidal functor `F : C ⥤ D` sends an exact pairing of `X` and `Y` to an exact pairing of
`F X` and `F Y`: the evaluation and coevaluation are transported along the monoidal structure
isomorphisms of `F`. Consequently `F` preserves dualizable objects.

## Main definitions

- `CategoryTheory.ExactPairing.map`: the exact pairing of `F X` and `F Y` induced by an exact
  pairing of `X` and `Y`.

## Main statements

- `CategoryTheory.IsDualizable.map`: a monoidal functor preserves dualizable objects.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A monoidal functor `F` sends an exact pairing of `X` and `Y` to an exact pairing of `F X`
and `F Y`, with coevaluation `𝟙_ ⟶ F 𝟙_ ⟶ F (X ⊗ Y) ⟶ F X ⊗ F Y` and evaluation
`F Y ⊗ F X ⟶ F (Y ⊗ X) ⟶ F 𝟙_ ⟶ 𝟙_`. -/
@[instance_reducible]
def ExactPairing.map (X Y : C) [ExactPairing X Y] : ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' := ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  evaluation' := μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  coevaluation_evaluation' := by
    have key : F.obj Y ◁ (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫
        (α_ (F.obj Y) (F.obj X) (F.obj Y)).inv ≫ (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) ▷ F.obj Y =
        (F.obj Y ◁ ε F ≫ μ F Y (𝟙_ C)) ≫
          F.map (Y ◁ η_ X Y ≫ (α_ Y X Y).inv ≫ ε_ X Y ▷ Y) ≫ (δ F (𝟙_ C) Y ≫ η F ▷ F.obj Y) := by
      simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_associator_inv, Functor.Monoidal.map_whiskerRight,
        Category.assoc, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
        Functor.Monoidal.μ_δ_assoc]
    rw [key, ExactPairing.coevaluation_evaluation]
    simp
  evaluation_coevaluation' := by
    have key : (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ▷ F.obj X ≫
        (α_ (F.obj X) (F.obj Y) (F.obj X)).hom ≫ F.obj X ◁ (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) =
        (ε F ▷ F.obj X ≫ μ F (𝟙_ C) X) ≫
          F.map (η_ X Y ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε_ X Y) ≫ (δ F X (𝟙_ C) ≫ F.obj X ◁ η F) := by
      simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_associator, Functor.Monoidal.map_whiskerRight,
        Category.assoc, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
        Functor.Monoidal.μ_δ_assoc]
    rw [key, ExactPairing.evaluation_coevaluation]
    simp

/-- A monoidal functor preserves dualizable objects. -/
theorem IsDualizable.map {X : C} (hX : IsDualizable X) : IsDualizable (F.obj X) := by
  obtain ⟨_⟩ := hX
  exact ⟨{ rightDual := F.obj Xᘁ
           exact := ExactPairing.map F X Xᘁ }⟩

end CategoryTheory
