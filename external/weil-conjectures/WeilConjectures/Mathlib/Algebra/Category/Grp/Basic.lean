/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# The reduction `ℤ ⟶ ℤ/n` in `AddCommGrpCat`

`AddCommGrpCat.uliftIntToZMod n` is the reduction `ℤ ⟶ ℤ/n` of (universe-lifted) abelian groups,
`ℤ` being written `ℤ/0`.
-/

@[expose] public section

universe u

namespace AddCommGrpCat

variable (n : ℕ)

/-- The reduction `ℤ ⟶ ℤ/n` of abelian groups, `ℤ` being written `ℤ/0`. -/
noncomputable def uliftIntToZMod :
    AddCommGrpCat.of (ULift.{u} (ZMod 0)) ⟶ AddCommGrpCat.of (ULift.{u} (ZMod n)) :=
  ofHom ((AddEquiv.ulift.symm : ZMod n ≃+ ULift.{u} (ZMod n)).toAddMonoidHom.comp
    ((ZMod.castHom (dvd_zero n) (ZMod n)).toAddMonoidHom.comp
      (AddEquiv.ulift : ULift.{u} (ZMod 0) ≃+ ZMod 0).toAddMonoidHom))

/-- The reduction `ℤ ⟶ ℤ/n` sends `1` to `1`. -/
lemma uliftIntToZMod_apply_one :
    (uliftIntToZMod.{u} n).hom (ULift.up 1) = ULift.up ((1 : ℕ) : ZMod n) :=
  ULift.ext ((map_one (ZMod.castHom (dvd_zero n) (ZMod n))).trans Nat.cast_one.symm)

end AddCommGrpCat
