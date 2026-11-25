/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! Definitions for canonical arithmetic restriction of strict derived towers. -/

@[expose] public section

set_option autoImplicit false

universe a b w uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.StrictTowerArithmetic

/-- The paper's level `e(n+1)`, encoded by its predecessor in `ℕ`.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
def index (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ e * (n + 1) - 1
      monotone' := fun _ _ h ↦ Nat.sub_le_sub_right (Nat.mul_le_mul_left e
        (Nat.add_le_add_right h 1)) 1 }).monotone.functor.op

/-- Exact restriction of strict towers along the arithmetic index functor.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
abbrev restriction (A : Type a) [Category.{b} A] (e : ℕ) :
    (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ A).obj (index e)

/-- Restriction on complexes of strict towers, before localization.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
abbrev complexRestriction (A : Type a) [Category.{b} A] [Abelian A] (e : ℕ) :=
  (restriction A e).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical derived restriction, induced by the exact restriction functor.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable abbrev derivedRestriction (A : Type a) [Category.{b} A] [Abelian A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] (e : ℕ) :=
  (restriction A e).mapDerivedCategory

/-- Coordinate selection on the source product of the Roos differential.
Source: Stacks Tag 0H9K, map φ′
(blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable def selection {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (e : ℕ) (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (∏ᶜ fun n : ℕ ↦ X.obj (op n)) ⟶
      ∏ᶜ (fun n : ℕ ↦ X.obj ((index e).obj (op n))) :=
  Pi.lift (fun n ↦ Pi.π (fun i : ℕ ↦ X.obj (op i)) (e * (n + 1) - 1))

/-- Finite-block summation on the target product of the Roos differential.
The summand `k` is the original level `e(n+1)+k`, for `0 ≤ k < e`.
Source: Stacks Tag 0H9K, map φ″
(blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable def block {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (e : ℕ) (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (∏ᶜ fun n : ℕ ↦ X.obj (op n)) ⟶
      ∏ᶜ (fun n : ℕ ↦ X.obj ((index e).obj (op n))) :=
  Pi.lift (fun n ↦ ∑ k ∈ Finset.range e,
    Pi.π (fun i : ℕ ↦ X.obj (op i)) (e * (n + 1) - 1 + k) ≫
      X.map (homOfLE (Nat.le_add_right (e * (n + 1) - 1) k)).op)

/-- The existing termwise inverse-limit functor, for the normalization of its derived unit.
Source: Stacks Tag 0941 (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable abbrev limitComplex (A : Type a) [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Ordinary limit restriction, degree by degree, using the actual limit cone.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable def limitMap {A : Type a} [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] (e : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (limitComplex A).obj X ⟶ (limitComplex A).obj ((complexRestriction A e).obj X) where
  f i := limit.pre (X.X i) (index e)
  comm' i j _ := by
    exact (limit.map_pre (X.d i j) (index e)).symm

/-- The existing transition differential, applied to the evaluated tower complex.
Source: Stacks Tags 08TC and 0H9K
(blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable abbrev boundary {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
  towerTransitionEndomorphism (K := fun n : ℕ ↦ X.asFunctor.obj (op n))
    (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)

/-- Mathlib's actual mapping cocone of the existing transition differential.
Source: Stacks Tags 08TC and 0941
(blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable abbrev model {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
  CochainComplex.mappingCocone (boundary X)

end CategoryTheory.StrictTowerArithmetic
