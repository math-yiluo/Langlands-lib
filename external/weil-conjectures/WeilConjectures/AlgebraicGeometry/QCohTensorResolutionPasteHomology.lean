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

/-- Paste a chain-level homology square with an extension-homology square. -/
theorem tensorResolution_paste_homology
    {C : Type*} [Category C]
    {A B D E F G H I : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (e : B ⟶ G) (f : G ⟶ H) (g : H ⟶ F)
    (t : A ⟶ I) (u : I ⟶ H)
    (h₁ : b ≫ c ≫ d = e ≫ f ≫ g)
    (h₂ : a ≫ e ≫ f = t ≫ u) :
    a ≫ b ≫ c ≫ d = t ≫ u ≫ g := by
  calc
    a ≫ b ≫ c ≫ d = a ≫ (b ≫ c ≫ d) := by rfl
    _ = a ≫ (e ≫ f ≫ g) := by rw [h₁]
    _ = (a ≫ e ≫ f) ≫ g := by simp only [Category.assoc]
    _ = (t ≫ u) ≫ g := by rw [h₂]
    _ = t ≫ u ≫ g := by simp only [Category.assoc]

end AlgebraicGeometry
