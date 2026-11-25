/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

/-!
# Blueprint statements

def-weil-derived-limit.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- def-weil-derived-limit. -/
def IsDerivedLimitTriangle {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧) : Prop :=
  Triangle.mk p (towerTransitionEndomorphism f) δ ∈ distTriang C

/-- def-weil-derived-limit. -/
def IsDerivedLimit {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n) (L : C) : Prop :=
  ∃ (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
    IsDerivedLimitTriangle f L p δ

end CategoryTheory
