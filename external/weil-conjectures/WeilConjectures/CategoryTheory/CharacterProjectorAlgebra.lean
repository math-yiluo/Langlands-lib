/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Tactic.LinearCombination

/-! # Products of finite character eigenspaces -/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : Type w} [CommRing K] [Linear K C]
  {G : Type t} [AddCommGroup G] [Fintype G] [Invertible (Fintype.card G : K)]
  {P : C} (τ : G → (P ⟶ P))
  (hτ : ∀ a b, τ a ≫ τ b = τ (a + b))

include hτ

private theorem eigen (χ : AddChar G K) (b : G) :
    (∑ a : G, (⅟(Fintype.card G : K) * χ (-a)) • τ a) ≫ τ b =
      χ b • (∑ a : G, (⅟(Fintype.card G : K) * χ (-a)) • τ a) := by
  classical
  simp only [Preadditive.sum_comp, Linear.smul_comp, hτ, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addRight b) _ _ fun a ↦ ?_
  simp only [Equiv.coe_addRight, neg_add_rev]
  congr 1
  have h : χ b * χ (-b) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [AddChar.map_add_eq_mul]
  linear_combination (-(⅟(Fintype.card G : K) * χ (-a))) * h

private theorem image_eigen (χ : AddChar G K) (b : G) :
    image.ι (∑ a : G, (⅟(Fintype.card G : K) * χ (-a)) • τ a) ≫ τ b =
      χ b • image.ι (∑ a : G, (⅟(Fintype.card G : K) * χ (-a)) • τ a) := by
  rw [← cancel_epi (factorThruImage _), image.fac_assoc, Linear.comp_smul, image.fac]
  exact eigen τ hτ χ b

/-- Multiplication preserving a finite translation action sends products of character
images into the image of the product character, and constant sections into the trivial image.

Source: latest blueprint `prop-kernel-lisse.proof.md`, multiplication of eigensections
(blueprint: lem-kernel-character-projector-algebra).

Proof. Reindexing the projector sum proves `eχ τ(b) = χ(b)eχ`, hence the image inclusion
has the same eigenvalue after cancellation of its image epimorphism. Equivariance and
bilinearity make a product of eigensections have eigenvalue `χ(b)χ'(b)`. Averaging with
weights `(χχ')(-b)/|G|` fixes it, because the character factors cancel and the normalized
sum is one. Invariant constant sections satisfy the same computation for the trivial
character. Neither a nontrivial character nor a nonzero coefficient ring is required. -/
theorem characterProjector_products_fixed
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (m : P ⊗ P ⟶ P) (η : 𝟙_ C ⟶ P)
    (hm : ∀ a, m ≫ τ a = (τ a ⊗ₘ τ a) ≫ m)
    (hη : ∀ a, η ≫ τ a = η) (χ χ' : AddChar G K) :
    let e := fun ψ : AddChar G K ↦ ∑ a : G, (⅟(Fintype.card G : K) * ψ (-a)) • τ a
    ((image.ι (e χ) ⊗ₘ image.ι (e χ')) ≫ m) ≫ e (χ * χ') =
        (image.ι (e χ) ⊗ₘ image.ι (e χ')) ≫ m ∧
      η ≫ e 1 = η := by
  classical
  dsimp only
  let e := fun ψ : AddChar G K ↦ ∑ a : G, (⅟(Fintype.card G : K) * ψ (-a)) • τ a
  let u := (image.ι (e χ) ⊗ₘ image.ι (e χ')) ≫ m
  have hu (a : G) : u ≫ τ a = (χ a * χ' a) • u := by
    dsimp only [u]
    rw [Category.assoc, hm, ← Category.assoc, tensorHom_comp_tensorHom,
      image_eigen τ hτ, image_eigen τ hτ]
    simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight,
      MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
    rfl
  have hc (a : G) : (⅟(Fintype.card G : K) * (χ * χ') (-a)) * (χ a * χ' a) =
      ⅟(Fintype.card G : K) := by
    rw [mul_assoc, ← AddChar.mul_apply, ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, mul_one]
  constructor
  · change u ≫ e (χ * χ') = u
    dsimp only [e]
    rw [Preadditive.comp_sum]
    simp only [Linear.comp_smul, hu, smul_smul, hc, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_invOf_self, one_smul]
  · change η ≫ e 1 = η
    dsimp only [e]
    rw [Preadditive.comp_sum]
    simp only [Linear.comp_smul, hη, AddChar.one_apply, mul_one, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_invOf_self, one_smul]

end CategoryTheory
