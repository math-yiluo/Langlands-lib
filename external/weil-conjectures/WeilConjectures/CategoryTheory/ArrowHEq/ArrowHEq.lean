/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-! # Heterogeneous equality of arrows with their endpoints recorded -/

@[expose] public section
set_option autoImplicit false
universe u v
namespace CategoryTheory

/-- Equality of arrows together with equality of their source and target objects.
Unlike heterogeneous equality of the arrow values alone, this relation can be composed.
Source: categorical equality transport, Mathlib `heq_comp`.
(blueprint: def-cat-arrow-heq-endpoints). -/
structure ArrowHEq {C : Type u} [Category.{v} C]
    {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') : Prop where
  source_eq : A = A'
  target_eq : B = B'
  heq : HEq f g

namespace ArrowHEq
variable {C : Type u} [Category.{v} C]

/-- An arrow agrees with itself, including its endpoints.
Source: equality reflexivity (blueprint: def-cat-arrow-heq-endpoints). -/
protected theorem refl {A B : C} (f : A ⟶ B) : ArrowHEq f f :=
  ⟨rfl, rfl, HEq.rfl⟩

/-- Reversing an endpoint-recording arrow equality.
Source: equality symmetry (blueprint: def-cat-arrow-heq-endpoints). -/
protected theorem symm {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (h : ArrowHEq f g) : ArrowHEq g f :=
  ⟨h.source_eq.symm, h.target_eq.symm, h.heq.symm⟩

/-- Transitivity preserves both endpoint equations.
Source: equality transitivity (blueprint: def-cat-arrow-heq-endpoints). -/
protected theorem trans {A B A' B' A'' B'' : C}
    {f : A ⟶ B} {g : A' ⟶ B'} {k : A'' ⟶ B''}
    (h : ArrowHEq f g) (h' : ArrowHEq g k) : ArrowHEq f k :=
  ⟨h.source_eq.trans h'.source_eq, h.target_eq.trans h'.target_eq, h.heq.trans h'.heq⟩

/-- Endpoint-recording equalities can be composed.
Source: Mathlib `heq_comp` (blueprint: def-cat-arrow-heq-endpoints). -/
protected theorem comp {A B D A' B' D' : C}
    {f : A ⟶ B} {g : B ⟶ D} {f' : A' ⟶ B'} {g' : B' ⟶ D'}
    (h : ArrowHEq f f') (k : ArrowHEq g g') : ArrowHEq (f ≫ g) (f' ≫ g') :=
  ⟨h.source_eq, k.target_eq, heq_comp h.source_eq h.target_eq k.target_eq h.heq k.heq⟩

/-- A functor preserves endpoint-recording equalities.
Source: functorial equality transport (blueprint: def-cat-arrow-heq-endpoints). -/
protected theorem map {D : Type*} [Category D] (F : C ⥤ D)
    {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'} (h : ArrowHEq f g) :
    ArrowHEq (F.map f) (F.map g) := by
  obtain ⟨rfl, rfl, h⟩ := h
  have := eq_of_heq h
  subst g
  exact ArrowHEq.refl _

/-- Endpoint-recorded equality transports any predicate on arrows.
Source: equality elimination (blueprint: def-cat-arrow-heq-endpoints). -/
protected theorem transport {P : ∀ {A B : C}, (A ⟶ B) → Prop}
    {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (h : ArrowHEq f g) (hf : P f) : P g := by
  rcases h with ⟨rfl, rfl, h⟩
  cases eq_of_heq h
  exact hf

end ArrowHEq
end CategoryTheory
