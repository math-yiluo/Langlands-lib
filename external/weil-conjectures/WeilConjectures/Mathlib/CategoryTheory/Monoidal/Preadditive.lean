/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# The pointwise monoidal structure on a functor category is preadditive

If `D` is a preadditive monoidal category in which the tensor product is additive in each
variable, then the pointwise monoidal structure on a functor category `C ⥤ D`
(`CategoryTheory.Monoidal.functorCategoryMonoidal`) is again preadditive: whiskering,
tensoring and addition of natural transformations are all computed objectwise, so each
`MonoidalPreadditive` axiom follows componentwise from the corresponding axiom in `D`.

We also record that whiskering commutes with `ℤ`-scalar multiplication
(`zsmul_whiskerRight`, `whiskerLeft_zsmul`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Monoidal

open MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  [MonoidalCategory.{v₂} D] [Preadditive D] [MonoidalPreadditive D]

instance functorCategoryMonoidalPreadditive : MonoidalPreadditive (C ⥤ D) where
  whiskerLeft_zero := by intros; ext; simp
  zero_whiskerRight := by intros; ext; simp
  whiskerLeft_add := by intros; ext; simp
  add_whiskerRight := by intros; ext; simp

end CategoryTheory.Monoidal

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

theorem zsmul_whiskerRight {X Y : C} (n : ℤ) (f : X ⟶ Y) (Z : C) :
    (n • f) ▷ Z = n • (f ▷ Z) :=
  Functor.map_zsmul (tensorRight Z)

theorem whiskerLeft_zsmul (X : C) {Y Z : C} (n : ℤ) (f : Y ⟶ Z) :
    X ◁ (n • f) = n • (X ◁ f) :=
  Functor.map_zsmul (tensorLeft X)

end CategoryTheory
