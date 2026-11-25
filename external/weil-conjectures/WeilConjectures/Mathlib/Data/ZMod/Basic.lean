/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Pairing `ZMod q` with `q`-torsion elements

Given an additive map `f : B →+ A` whose values are killed by `q` and an additive map
`c : M →+ ZMod q`, `AddMonoidHom.zmodValNsmul f hf c : B →+ (M →+ A)` sends `b` to
`m ↦ (c m).val • f b`.
-/

@[expose] public section

/-- Given an additive map `f : B →+ A` whose values are killed by `q` and an additive map
`c : M →+ ZMod q`, the additive map `B →+ (M →+ A)` sending `b` to `m ↦ (c m).val • f b`. -/
def AddMonoidHom.zmodValNsmul {M B A : Type*} [AddCommGroup M] [AddCommGroup B]
    [AddCommGroup A] {q : ℕ} [NeZero q] (f : B →+ A) (hf : ∀ b, q • f b = 0)
    (c : M →+ ZMod q) : B →+ (M →+ A) where
  toFun b :=
    { toFun m := (c m).val • f b
      map_zero' := by simp
      map_add' m m' := by
        rw [map_add, ZMod.val_add, ← nsmul_eq_mod_nsmul _ (hf b), add_nsmul] }
  map_zero' := by
    ext
    simp
  map_add' b b' := by
    ext
    simp

@[simp]
lemma AddMonoidHom.zmodValNsmul_apply_apply {M B A : Type*} [AddCommGroup M]
    [AddCommGroup B] [AddCommGroup A] {q : ℕ} [NeZero q] (f : B →+ A) (hf : ∀ b, q • f b = 0)
    (c : M →+ ZMod q) (b : B) (m : M) : f.zmodValNsmul hf c b m = (c m).val • f b :=
  rfl
