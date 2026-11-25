/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!

# The category of module objects is preadditive

If `C` is a preadditive monoidal category whose tensor product is additive in each variable
(`MonoidalPreadditive C`), then for every algebra object `R : C` the category `Mod C R` of left
`R`-module objects is preadditive: sums and negatives of `R`-linear morphisms are computed in `C`
(`WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`). This file adds the whiskering lemmas
for negation, subtraction and scalar multiples, and the simp lemmas for differences and scalar
multiples of `R`-linear morphisms.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Preadditive

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

@[simp]
lemma whiskerLeft_neg (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ (-f) = -(X ◁ f) :=
  (tensorLeft X).map_neg

@[simp]
lemma neg_whiskerRight {Y Z : C} (f : Y ⟶ Z) (X : C) : (-f) ▷ X = -(f ▷ X) :=
  (tensorRight X).map_neg

@[simp]
lemma whiskerLeft_sub (X : C) {Y Z : C} (f g : Y ⟶ Z) : X ◁ (f - g) = X ◁ f - X ◁ g :=
  (tensorLeft X).map_sub

@[simp]
lemma sub_whiskerRight {Y Z : C} (f g : Y ⟶ Z) (X : C) : (f - g) ▷ X = f ▷ X - g ▷ X :=
  (tensorRight X).map_sub

@[simp]
lemma whiskerLeft_nsmul (X : C) {Y Z : C} (n : ℕ) (f : Y ⟶ Z) : X ◁ (n • f) = n • (X ◁ f) :=
  (tensorLeft X).map_nsmul

@[simp]
lemma nsmul_whiskerRight {Y Z : C} (n : ℕ) (f : Y ⟶ Z) (X : C) : (n • f) ▷ X = n • (f ▷ X) :=
  (tensorRight X).map_nsmul

@[simp]
lemma whiskerLeft_zsmul (X : C) {Y Z : C} (n : ℤ) (f : Y ⟶ Z) : X ◁ (n • f) = n • (X ◁ f) :=
  (tensorLeft X).map_zsmul

@[simp]
lemma zsmul_whiskerRight {Y Z : C} (n : ℤ) (f : Y ⟶ Z) (X : C) : (n • f) ▷ X = n • (f ▷ X) :=
  (tensorRight X).map_zsmul

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] {R : C} [MonObj R]

variable {M N : Mod C R}

@[simp] lemma sub_hom (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

@[simp] lemma nsmul_hom (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

@[simp] lemma zsmul_hom (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

end CategoryTheory.Mod
