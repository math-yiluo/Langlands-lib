/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# `Ext` groups as modules over a ring acting on the target

Let `C` be an abelian category and `φ : R →+* End Y` an action of a ring `R` on an object `Y`
(e.g. the action of `ℤ_ℓ` on the pro-étale sheaf `C(-, ℤ_ℓ)`). Then every `Ext X Y n` is an
`R`-module, `r • x = x ∘ φ r` (`CategoryTheory.Abelian.Ext.moduleOfRingHom`). Postcomposition
with a morphism `g : Y ⟶ Y'` commuting with the actions is `R`-linear
(`CategoryTheory.Abelian.Ext.postcompLinearMap`). The action of a natural number is the
`ℕ`-multiple (`CategoryTheory.Abelian.Ext.smul_natCast_eq_nsmul`), so additive maps such as the
connecting maps of long exact sequences commute with it.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {R : Type*} [Ring R]

/-- The `R`-module structure on `Ext X Y n` induced by an action `φ : R →+* End Y` of `R` on `Y`:
`r • x = x ∘ φ r`. -/
noncomputable abbrev moduleOfRingHom {X Y : C} (φ : R →+* End Y) (n : ℕ) :
    Module R (Ext X Y n) where
  smul r x := x.comp (mk₀ (φ r).asHom) (add_zero n)
  one_smul x := by
    change x.comp (mk₀ (φ 1).asHom) (add_zero n) = x
    rw [map_one, End.one_asHom, comp_mk₀_id]
  mul_smul r s x := by
    change x.comp (mk₀ (φ (r * s)).asHom) (add_zero n) =
      (x.comp (mk₀ (φ s).asHom) (add_zero n)).comp (mk₀ (φ r).asHom) (add_zero n)
    rw [map_mul, End.mul_asHom, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]
  smul_zero r := Ext.zero_comp X n (mk₀ (φ r).asHom) n (add_zero n)
  smul_add r x y := Ext.add_comp x y (mk₀ (φ r).asHom) (add_zero n)
  add_smul r s x := by
    change x.comp (mk₀ (φ (r + s)).asHom) (add_zero n) =
      x.comp (mk₀ (φ r).asHom) (add_zero n) + x.comp (mk₀ (φ s).asHom) (add_zero n)
    rw [map_add, End.add_asHom, mk₀_add, Ext.comp_add]
  zero_smul x := by
    change x.comp (mk₀ (φ 0).asHom) (add_zero n) = 0
    rw [map_zero, End.zero_asHom, mk₀_zero, Ext.comp_zero]

lemma moduleOfRingHom_smul_def {X Y : C} (φ : R →+* End Y) (n : ℕ) (r : R) (x : Ext X Y n) :
    letI := moduleOfRingHom (X := X) φ n
    r • x = x.comp (mk₀ ((φ r)).asHom) (add_zero n) :=
  rfl


/-- The action of a natural number is the `ℕ`-multiple. -/
lemma smul_natCast_eq_nsmul {X Y : C} (φ : R →+* End Y) (n : ℕ) (k : ℕ) (x : Ext X Y n) :
    letI := moduleOfRingHom (X := X) φ n
    (k : R) • x = k • x := by
  let := moduleOfRingHom (X := X) φ n
  exact Nat.cast_smul_eq_nsmul R k x

/-- Postcomposition with a morphism `g : Y ⟶ Y'` commuting with actions `φ`, `φ'` of `R` is an
`R`-linear map `Ext X Y n ⟶ Ext X Y' n`. -/
noncomputable def postcompLinearMap {X Y Y' : C} (φ : R →+* End Y) (φ' : R →+* End Y')
    (g : Y ⟶ Y') (hg : ∀ r, (φ r).asHom ≫ g = g ≫ (φ' r).asHom) (n : ℕ) :
    letI := moduleOfRingHom (X := X) φ n
    letI := moduleOfRingHom (X := X) φ' n
    Ext X Y n →ₗ[R] Ext X Y' n :=
  letI := moduleOfRingHom (X := X) φ n
  letI := moduleOfRingHom (X := X) φ' n
  { toFun x := x.comp (mk₀ g) (add_zero n)
    map_add' x y := add_comp _ _ _ _
    map_smul' r x := by
      change (x.comp (mk₀ (φ r).asHom) (add_zero n)).comp (mk₀ g) (add_zero n) =
        (x.comp (mk₀ g) (add_zero n)).comp (mk₀ (φ' r).asHom) (add_zero n)
      rw [comp_assoc_of_third_deg_zero, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀,
        mk₀_comp_mk₀, hg] }

lemma postcompLinearMap_apply {X Y Y' : C} (φ : R →+* End Y) (φ' : R →+* End Y')
    (g : Y ⟶ Y') (hg : ∀ r, (φ r).asHom ≫ g = g ≫ (φ' r).asHom) (n : ℕ) (x : Ext X Y n) :
    postcompLinearMap (X := X) φ φ' g hg n x = x.comp (mk₀ g) (add_zero n) :=
  rfl


end CategoryTheory.Abelian.Ext
