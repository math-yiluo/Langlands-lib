/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section
open CategoryTheory
namespace AlgebraicGeometry

/-- Compose a summand square, a factor square, and a source comparison. -/
theorem tensorResolution_three_squares
    {C : Type*} [Category C]
    {A B D E F G H I J K : C}
    (x : A ⟶ B) (u : B ⟶ D) (v : D ⟶ E) (w : E ⟶ F)
    (r : D ⟶ G) (s : G ⟶ H) (t : H ⟶ F)
    (r' : B ⟶ I) (s' : I ⟶ J) (u' : J ⟶ H)
    (z : A ⟶ K) (y : K ⟶ J)
    (h₁ : x ≫ u ≫ v ≫ w = x ≫ u ≫ r ≫ s ≫ t)
    (h₂ : u ≫ r ≫ s = r' ≫ s' ≫ u')
    (h₃ : x ≫ r' ≫ s' = z ≫ y) :
    x ≫ u ≫ v ≫ w = z ≫ y ≫ u' ≫ t := by
  calc
    x ≫ u ≫ v ≫ w = x ≫ u ≫ r ≫ s ≫ t := h₁
    _ = x ≫ (u ≫ r ≫ s) ≫ t := by simp only [Category.assoc]
    _ = x ≫ (r' ≫ s' ≫ u') ≫ t := by rw [h₂]
    _ = (x ≫ r' ≫ s') ≫ u' ≫ t := by simp only [Category.assoc]
    _ = (z ≫ y) ≫ u' ≫ t := by rw [h₃]
    _ = z ≫ y ≫ u' ≫ t := by simp only [Category.assoc]

end AlgebraicGeometry
