/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# `Ext`-groups as morphisms in the derived category

The `Ext`-groups `Ext^n(X, Y)` of an abelian category are the morphisms `X ⟶ Y[n]` in the
derived category, and they vanish in positive degrees when `X` is projective.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **Extensions.** The `n`-th `Ext`-group `Ext^n(X, Y)` (Mathlib's
`CategoryTheory.Abelian.Ext`) is in bijection with the group of morphisms `X ⟶ Y[n]` in the
derived category, and it vanishes for `n ≥ 1` when `X` is projective.

(blueprint: `def-pc-ext`) -/
theorem nonempty_equiv_shiftedHom [HasDerivedCategory.{w} C] (X Y : C) (n : ℕ) :
    Nonempty (Ext.{w} X Y n ≃ ShiftedHom ((singleFunctor C 0).obj X)
      ((singleFunctor C 0).obj Y) (n : ℤ)) ∧
      (Projective X → 0 < n → Subsingleton (Ext.{w} X Y n)) := by
  refine ⟨⟨homEquiv⟩, fun _ hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simpa using subsingleton_of_projective X Y m

end CategoryTheory.Abelian.Ext
