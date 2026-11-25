/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# Powers of intertwined endomorphisms; units and inverses in `Aut X`

A morphism `p : Y ⟶ X` intertwining endomorphisms `a` of `Y` and `b` of `X`
(`a ≫ p = p ≫ b`) intertwines their powers in the endomorphism monoids.

## Main statements

- `CategoryTheory.End.asHom_pow_comp_eq_comp_asHom_pow`: `a ^ m ≫ p = p ≫ b ^ m`.
- `CategoryTheory.Aut.one_hom`, `CategoryTheory.Aut.inv_hom`, `CategoryTheory.Aut.mul_hom`: the
  underlying morphisms of the unit, inverses and products in `Aut X`.
- `CategoryTheory.End.comp_pow_eq_pow_comp`: the same statement for monoid powers in `End`.
- `CategoryTheory.End.asHom_pow_comp_of_comp_eq`: if `a ≫ p = p` then `a ^ m ≫ p = p`.
-/

@[expose] public section

namespace CategoryTheory.Aut

variable {C : Type*} [Category* C] (X : C)

@[simp]
lemma one_hom : (1 : Aut X).asIso.hom = 𝟙 X :=
  rfl

variable {X}

@[simp]
lemma inv_hom (f : Aut X) : f⁻¹.asIso.hom = f.asIso.inv :=
  rfl

@[simp]
lemma mul_hom (f g : Aut X) : (f * g).asIso.hom = g.asIso.hom ≫ f.asIso.hom :=
  rfl

end CategoryTheory.Aut

namespace CategoryTheory.End

variable {C : Type*} [Category* C] {X Y : C}

/-- A morphism `p` intertwining endomorphisms `a` and `b` (`a ≫ p = p ≫ b`) intertwines their
`m`-th powers. -/
lemma asHom_pow_comp_eq_comp_asHom_pow {a : Y ⟶ Y} {b : X ⟶ X} {p : Y ⟶ X}
    (h : a ≫ p = p ≫ b) (m : ℕ) :
    asHom (of a ^ m) ≫ p = p ≫ asHom (of b ^ m) := by
  induction m with
  | zero => simp [one_asHom]
  | succ m ih =>
    change asHom (of a ^ m * of a) ≫ p = p ≫ asHom (of b ^ m * of b)
    rw [mul_asHom, mul_asHom]
    change (a ≫ asHom (of a ^ m)) ≫ p = p ≫ b ≫ asHom (of b ^ m)
    rw [Category.assoc, ih, reassoc_of% h]

/-- If `x ≫ A = S ≫ x` then `x ≫ A ^ j = S ^ j ≫ x` for the monoid powers in `End`. -/
lemma comp_pow_eq_pow_comp {W X : C} (x : W ⟶ X) (A : End X)
    (S : End W) (h : x ≫ A.asHom = S.asHom ≫ x) (j : ℕ) :
    x ≫ ((A ^ j : End X)).asHom = ((S ^ j : End W)).asHom ≫ x := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero, End.one_asHom, End.one_asHom, Category.comp_id, Category.id_comp]
  | succ j ih =>
    rw [pow_succ, pow_succ, End.mul_asHom, End.mul_asHom, ← Category.assoc, h, Category.assoc, ih,
      Category.assoc]

/-- If `a ≫ p = p`, then `a ^ m ≫ p = p` for every `m`. -/
lemma asHom_pow_comp_of_comp_eq {a : Y ⟶ Y} {p : Y ⟶ X} (h : a ≫ p = p) (m : ℕ) :
    asHom (of a ^ m) ≫ p = p := by
  refine (asHom_pow_comp_eq_comp_asHom_pow (b := 𝟙 X) (h.trans (Category.comp_id p).symm)
    m).trans ?_
  rw [show of (𝟙 X) ^ m = 1 from one_pow m]
  exact Category.comp_id p

end CategoryTheory.End
