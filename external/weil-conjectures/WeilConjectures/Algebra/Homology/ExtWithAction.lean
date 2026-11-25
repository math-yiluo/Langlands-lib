/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# `Ext`-groups with an action on the target

Let `C` be an abelian category, `A` a commutative ring and `F` an object of `C` with an action
`ρ : A →+* End F` of `A`. For every object `P`, the group `Ext P F n` is an `A`-module, with
`a • x = ρ(a)_* x` (`CategoryTheory.Abelian.Ext.WithAction`).

For the sheaf cohomology `H^n(X, ℱ) = Ext^n(ℤ, ℱ)` of a sheaf of modules `ℱ` on a scheme, with
`ρ` given by multiplication by global functions, this is the module structure used in flat base
change (`AlgebraicGeometry.Scheme.Modules.nonempty_H_baseChange_linearEquiv`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section Action

variable {A : Type*} [CommRing A] {F : C} (ρ : A →+* End F)

/-- `Ext P F n` with the action of `A` induced by an action `ρ : A →+* End F` of `A` on `F`,
`a • x = ρ(a)_* x`. -/
@[nolint unusedArguments]
def WithAction (_ρ : A →+* End F) (P : C) (n : ℕ) : Type w := Ext P F n

namespace WithAction

noncomputable instance (P : C) (n : ℕ) : AddCommGroup (WithAction ρ P n) :=
  inferInstanceAs (AddCommGroup (Ext P F n))

/-- The action of `A` on `Ext P F n` induced by `ρ`, as a ring homomorphism to the additive
endomorphisms. -/
noncomputable def smulEnd (P : C) (n : ℕ) : A →+* AddMonoid.End (Ext P F n) where
  toFun a := (mk₀ (ρ a).asHom).postcomp P (add_zero n)
  map_one' := by
    ext x
    change x.comp (mk₀ (ρ 1).asHom) (add_zero n) = x
    rw [map_one, End.one_asHom]
    exact comp_mk₀_id x
  map_mul' a b := by
    ext x
    change x.comp (mk₀ (ρ (a * b)).asHom) (add_zero n) =
      (x.comp (mk₀ (ρ b).asHom) (add_zero n)).comp (mk₀ (ρ a).asHom) (add_zero n)
    rw [map_mul, End.mul_asHom, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]
  map_zero' := by
    ext x
    change x.comp (mk₀ (ρ 0).asHom) (add_zero n) = 0
    rw [map_zero, End.zero_asHom, mk₀_zero]
    exact comp_zero _ _ _ _ _
  map_add' a b := by
    ext x
    change x.comp (mk₀ (ρ (a + b)).asHom) (add_zero n) =
      x.comp (mk₀ (ρ a).asHom) (add_zero n) + x.comp (mk₀ (ρ b).asHom) (add_zero n)
    rw [map_add, End.add_asHom, mk₀_add]
    exact comp_add _ _ _ _

noncomputable instance (P : C) (n : ℕ) : Module A (WithAction ρ P n) :=
  Module.compHom (Ext P F n) (smulEnd ρ P n)

/-- The identification of `WithAction ρ P n` with `Ext P F n`. -/
noncomputable def toExt {P : C} {n : ℕ} : WithAction ρ P n ≃+ Ext P F n := AddEquiv.refl _

lemma toExt_smul {P : C} {n : ℕ} (a : A) (x : WithAction ρ P n) :
    toExt ρ (a • x) = (toExt ρ x).comp (mk₀ ((ρ a)).asHom) (add_zero n) :=
  rfl

end WithAction

end Action

end CategoryTheory.Abelian.Ext
