/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Integers acting by zero on a derived category

If an integer `m` acts by zero on every object of an abelian category `A`, then it acts by zero
on every object of the derived category `D(A)` (`DerivedCategory.zsmul_id_eq_zero`).
-/

@[expose] public section

open CategoryTheory Limits

/-- In the derived category of an abelian category on which an integer `m` acts by zero, `m`
acts by zero on every object. -/
lemma DerivedCategory.zsmul_id_eq_zero {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {m : ℤ} (hm : ∀ M : A, m • 𝟙 M = 0) (K : DerivedCategory A) :
    m • 𝟙 K = 0 := by
  let e := DerivedCategory.Q.objObjPreimageIso K
  have h₀ : m • 𝟙 (DerivedCategory.Q.objPreimage K) = 0 := by
    ext i
    simp [hm]
  have h : m • 𝟙 (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, h₀, Functor.map_zero]
  rw [← cancel_epi e.hom, Preadditive.comp_zsmul, Category.comp_id, Limits.comp_zero,
    ← Category.id_comp e.hom, ← Preadditive.zsmul_comp, h, Limits.zero_comp]
