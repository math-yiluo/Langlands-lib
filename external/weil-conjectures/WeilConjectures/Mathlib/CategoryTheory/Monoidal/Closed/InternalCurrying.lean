/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Naturality of internal currying

The internal currying isomorphism `C(x ⊗ y, z) ≅ C(y, C(x, z))`
(`MonoidalClosed.ihomCurryIso`) is natural in `x` and in `z`.
-/

@[expose] public section

universe u v

namespace CategoryTheory.MonoidalClosed

open Category MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The internal currying `C(x ⊗ y, z) ⟶ C(y, C(x, z))` is natural in `x`. -/
@[reassoc]
lemma pre_whiskerRight_app_comp_ihomCurry {x x' : C} (f : x' ⟶ x) (y z : C) [Closed x]
    [Closed x'] [Closed y] [Closed (x ⊗ y)] [Closed (x' ⊗ y)] :
    (pre (f ▷ y)).app z ≫ ihomCurry x' y z = ihomCurry x y z ≫ (ihom y).map ((pre f).app z) := by
  apply uncurry_injective
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right, uncurry_natural_left,
    uncurry_uncurry_ihomCurry, associator_inv_naturality_right_assoc, ← uncurry_eq, uncurry_pre,
    uncurry_eq (_ ≫ _), MonoidalCategory.whiskerLeft_comp_assoc, ← uncurry_eq, uncurry_pre,
    whisker_exchange_assoc, ← uncurry_eq, uncurry_uncurry_ihomCurry,
    associator_inv_naturality_left_assoc]

/-- The internal currying isomorphism `C(x ⊗ y, z) ≅ C(y, C(x, z))` is natural in `x`. -/
@[reassoc]
lemma pre_whiskerRight_app_comp_ihomCurryIso_hom {x x' : C} (f : x' ⟶ x) (y z : C) [Closed x]
    [Closed x'] [Closed y] [Closed (x ⊗ y)] [Closed (x' ⊗ y)] :
    (pre (f ▷ y)).app z ≫ (ihomCurryIso x' y z).hom =
      (ihomCurryIso x y z).hom ≫ (ihom y).map ((pre f).app z) :=
  pre_whiskerRight_app_comp_ihomCurry f y z

/-- The internal currying `C(x ⊗ y, z) ⟶ C(y, C(x, z))` is natural in `z`: the square
```
  C(x ⊗ y, z) ──── C(x ⊗ y, g) ────→ C(x ⊗ y, z')
       │                                   │
   ihomCurry                           ihomCurry
       ↓                                   ↓
  C(y, C(x, z)) ── C(y, C(x, g)) ──→ C(y, C(x, z'))
```
commutes. -/
@[reassoc]
lemma map_comp_ihomCurry (x y : C) [Closed x] [Closed y] [Closed (x ⊗ y)] {z z' : C}
    (g : z ⟶ z') :
    (ihom (x ⊗ y)).map g ≫ ihomCurry x y z' = ihomCurry x y z ≫ (ihom y).map ((ihom x).map g) := by
  apply uncurry_injective
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right, uncurry_natural_left, uncurry_natural_right,
    uncurry_uncurry_ihomCurry, uncurry_uncurry_ihomCurry, associator_inv_naturality_right_assoc,
    Category.assoc]
  simp only [ihom.ev_naturality]

/-- The internal currying isomorphism `C(x ⊗ y, z) ≅ C(y, C(x, z))` is natural in `z`. -/
@[reassoc]
lemma map_comp_ihomCurryIso_hom (x y : C) [Closed x] [Closed y] [Closed (x ⊗ y)] {z z' : C}
    (g : z ⟶ z') :
    (ihom (x ⊗ y)).map g ≫ (ihomCurryIso x y z').hom =
      (ihomCurryIso x y z).hom ≫ (ihom y).map ((ihom x).map g) :=
  map_comp_ihomCurry x y g

end CategoryTheory.MonoidalClosed
