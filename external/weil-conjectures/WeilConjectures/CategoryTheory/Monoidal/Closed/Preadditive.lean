/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Currying in a preadditive monoidal closed category

In a monoidal closed category `C` whose monoidal structure is compatible with a preadditive
structure (`MonoidalPreadditive C`), the internal hom functors `ihom A` are additive, and
currying is an isomorphism of abelian groups `MonoidalClosed.curryAddEquiv`, so that currying
and uncurrying are compatible with sums, differences and multiplication by integers.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] {A B X Y : C}

instance (A : C) : (ihom A).Additive := (ihom.adjunction A).right_adjoint_additive

/-- Currying `A ⊗ X ⟶ Y` to `X ⟶ (ihom A).obj Y`, as an isomorphism of abelian groups. -/
def curryAddEquiv (A X Y : C) : (A ⊗ X ⟶ Y) ≃+ (X ⟶ (ihom A).obj Y) :=
  (ihom.adjunction A).homAddEquiv X Y

@[simp]
lemma curryAddEquiv_apply (f : A ⊗ X ⟶ Y) : curryAddEquiv A X Y f = curry f := rfl

@[simp]
lemma curryAddEquiv_symm_apply (f : X ⟶ (ihom A).obj Y) :
    (curryAddEquiv A X Y).symm f = uncurry f := rfl

lemma curry_add (f g : A ⊗ X ⟶ Y) : curry (f + g) = curry f + curry g :=
  map_add (curryAddEquiv A X Y) f g

lemma curry_sub (f g : A ⊗ X ⟶ Y) : curry (f - g) = curry f - curry g :=
  map_sub (curryAddEquiv A X Y) f g

lemma curry_zsmul (k : ℤ) (f : A ⊗ X ⟶ Y) : curry (k • f) = k • curry f :=
  map_zsmul (curryAddEquiv A X Y) k f

lemma curry_units_smul (k : ℤˣ) (f : A ⊗ X ⟶ Y) : curry (k • f) = k • curry f :=
  curry_zsmul (k : ℤ) f

lemma uncurry_add (f g : X ⟶ (ihom A).obj Y) : uncurry (f + g) = uncurry f + uncurry g :=
  map_add (curryAddEquiv A X Y).symm f g

lemma uncurry_sub (f g : X ⟶ (ihom A).obj Y) : uncurry (f - g) = uncurry f - uncurry g :=
  map_sub (curryAddEquiv A X Y).symm f g

lemma uncurry_zsmul (k : ℤ) (f : X ⟶ (ihom A).obj Y) : uncurry (k • f) = k • uncurry f :=
  map_zsmul (curryAddEquiv A X Y).symm k f

lemma uncurry_units_smul (k : ℤˣ) (f : X ⟶ (ihom A).obj Y) :
    uncurry (k • f) = k • uncurry f :=
  uncurry_zsmul (k : ℤ) f

@[simp]
lemma pre_zero_app (X : C) : (pre (0 : B ⟶ A)).app X = 0 :=
  uncurry_injective (by simp [uncurry_eq])

end CategoryTheory.MonoidalClosed
