/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Linear
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The pointwise monoidal structure on a functor category is linear

If `D` is an `R`-linear monoidal category whose tensor product is `R`-linear in each
variable, then the pointwise monoidal structure on a functor category `C ⥤ D`
(`CategoryTheory.Monoidal.functorCategoryMonoidal`) is again `R`-linear: whiskering,
tensoring and the scalar action on natural transformations are all computed objectwise,
so each `MonoidalLinear` axiom follows componentwise from the corresponding axiom in `D`.

The file also records that the two partial functors `X ⊗ -` and `- ⊗ X` of the curried tensor
product `curriedTensor D` are `R`-linear.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Monoidal

open MonoidalCategory

variable (R : Type*) [Semiring R] (C : Type u₁) [Category.{v₁} C] (D : Type u₂)
  [Category.{v₂} D] [MonoidalCategory.{v₂} D] [Preadditive D] [Linear R D]
  [MonoidalPreadditive D] [MonoidalLinear R D]

instance functorCategoryMonoidalLinear : MonoidalLinear R (C ⥤ D) where
  whiskerLeft_smul := by intros; ext; simp
  smul_whiskerRight := by intros; ext; simp

end CategoryTheory.Monoidal

namespace CategoryTheory

open MonoidalCategory

variable {R : Type*} [Semiring R] {D : Type*} [Category* D] [MonoidalCategory D] [Preadditive D]
  [Linear R D] [MonoidalPreadditive D] [MonoidalLinear R D]

instance curriedTensor_obj_linear (X : D) : ((curriedTensor D).obj X).Linear R where

instance curriedTensor_flip_obj_linear (X : D) : ((curriedTensor D).flip.obj X).Linear R where

end CategoryTheory
