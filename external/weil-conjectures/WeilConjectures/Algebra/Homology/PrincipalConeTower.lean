/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.StrictRoosModel

/-! # The augmented tower of powers of a chain endomorphism

Source: Stacks Tags 0A0E and 0941.
(auxiliary; not a blueprint node) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CochainComplex.PrincipalCone

variable {A : Type u} [Category.{v} A] [Abelian A]
  {P : CochainComplex A ℤ} (μ : End P)

/-- The positive-power cone at level n, representing exponent n+1.
Source: Stacks 0A0E (auxiliary; not a blueprint node). -/
def level (n : ℕ) := mappingCone (μ ^ (n + 1)).asHom

/-- The square (μ,1) between consecutive powers commutes.
Source: Stacks 0A0E (auxiliary; not a blueprint node).
Proof: the power recursion in the endomorphism monoid is composition. -/
theorem square (n : ℕ) :
    (μ ^ (n + 1 + 1)).asHom ≫ 𝟙 P = μ.asHom ≫ (μ ^ (n + 1)).asHom := by
  simpa only [Category.comp_id, End.mul_asHom] using
    congrArg End.asHom (pow_succ μ (n + 1))

/-- The transition acts by μ on the source and by 1 on the target.
Source: Stacks 0A0E (auxiliary; not a blueprint node). -/
def step (n : ℕ) : level μ (n + 1) ⟶ level μ n :=
  mappingCone.map _ _ μ.asHom (𝟙 P) (square μ n)

/-- The inverse tower, indexed by positive powers.
Source: Stacks 0A0E (auxiliary; not a blueprint node). -/
def tower : ℕᵒᵖ ⥤ CochainComplex A ℤ := CategoryTheory.Functor.ofOpSequence (step μ)

/-- The degree-zero maps respect the transitions.
Source: Stacks 0A0E (auxiliary; not a blueprint node).
Proof: the target map of each cone square is the identity. -/
theorem compatible (n : ℕ) :
    mappingCone.inr (μ ^ (n + 1 + 1)).asHom ≫ step μ n =
      mappingCone.inr (μ ^ (n + 1)).asHom := by
  simp [step, mappingCone.map]

variable [HasCountableProducts A]

/-- The product of degree-zero inclusions.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def productUnit : P ⟶ ∏ᶜ (fun n : ℕ ↦ (tower μ).obj (op n)) :=
  Pi.lift (fun n ↦ mappingCone.inr (μ ^ (n + 1)).asHom)

/-- One minus the transition shift.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def oneSubShift := towerTransitionEndomorphism
  (K := fun n : ℕ ↦ (tower μ).obj (op n)) (step μ)

/-- Compatibility annihilates one minus the shift.
Source: Stacks 0941 (auxiliary; not a blueprint node).
Proof: each product projection is the difference of consecutive compatible inclusions. -/
theorem productUnit_comp : productUnit μ ≫ oneSubShift μ = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [oneSubShift, towerTransitionEndomorphism, Preadditive.comp_sub,
    Category.comp_id, Preadditive.sub_comp, towerProductShift, Category.assoc,
    Pi.lift_comp_π, productUnit, Pi.lift_comp_π_assoc, compatible, sub_self, zero_comp]

/-- The strict Roos completion of the cone tower.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def completion := mappingCocone (oneSubShift μ)

/-- The zero homotopy supplies the normalized Roos augmentation.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def unit : P ⟶ completion μ :=
  mappingCocone.lift _ (productUnit μ) 0 (by simp [productUnit_comp])

end CochainComplex.PrincipalCone
