/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive functors on finite elementary abelian groups

A finite abelian group killed by a prime `ℓ` is a finite direct sum of copies of `ℤ/ℓ`. Hence an
additive functor out of `AddCommGrpCat` which vanishes on `ℤ/ℓ` vanishes on every finite abelian
group killed by `ℓ` (blueprint `lemma-cohomology-near-two-transverse-divisors--1`, constant
coefficients).

## Main statements

- `AddCommGrpCat.isZero_obj_of_nsmul_eq_zero`
-/

@[expose] public section

universe v

open CategoryTheory Limits

/-- An additive functor out of `AddCommGrpCat` which vanishes on `ℤ/ℓ` vanishes on every finite
abelian group killed by `ℓ`, such a group being a finite direct sum of copies of `ℤ/ℓ`
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`). -/
theorem AddCommGrpCat.isZero_obj_of_nsmul_eq_zero {D : Type*} [Category D] [Preadditive D]
    [HasFiniteBiproducts D] (Φ : AddCommGrpCat.{v} ⥤ D) [Φ.Additive] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : IsZero (Φ.obj (AddCommGrpCat.of (ULift.{v} (ZMod ℓ)))))
    (A : AddCommGrpCat.{v}) [Finite A] (hA : ∀ a : A, ℓ • a = 0) : IsZero (Φ.obj A) := by
  have : Module (ZMod ℓ) A := AddCommGroup.zmodModule hA
  have : Module.Finite (ZMod ℓ) A := Module.Finite.of_finite
  let e : A ≅ ⨁ fun _ : Fin (Module.finrank (ZMod ℓ) A) ↦
      AddCommGrpCat.of (ULift.{v} (ZMod ℓ)) :=
    ((Module.finBasis (ZMod ℓ) A).equivFun.toAddEquiv.trans
      (AddEquiv.piCongrRight fun _ ↦ AddEquiv.ulift.symm)).toAddCommGrpIso ≪≫
      (AddCommGrpCat.biproductIsoPi _).symm
  refine IsZero.of_iso ?_ (Φ.mapIso e ≪≫ Φ.mapBiproduct _)
  rw [IsZero.iff_id_eq_zero]
  ext j
  exact h.eq_of_src _ _
