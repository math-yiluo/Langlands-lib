/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-! # Alpha-small and alpha-compact objects

Source: Krause, On Neeman's Well Generated Triangulated Categories (2001),
page 122, condition (G4) and the maximal class of alpha-small objects.
(blueprint: def-sfb-alpha-compact-object)
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C]

/-- Smallness measured by support in arbitrary coproducts, not by filtered colimits.
Source: Krause (2001), page 121, condition (G3).
(blueprint: def-sfb-alpha-compact-object) -/
def IsAlphaSmall (U : C) (α : Cardinal.{v}) : Prop :=
  ∀ (I : Type v) (Y : I → C) (f : U ⟶ ∐ Y),
    ∃ (J : Set I), HasCardinalLT J α ∧
      ∃ g : U ⟶ ∐ fun j : J ↦ Y j,
        g ≫ Sigma.desc (fun j : J ↦ Sigma.ι Y j) = f

/-- Krause's factorization condition (G4) for a class of objects.
Source: Krause (2001), page 122.
(blueprint: def-sfb-alpha-compact-object) -/
def ObjectProperty.IsCoproductFactorizationClass (S : ObjectProperty C) : Prop :=
  ∀ (U : C), S U → ∀ (I : Type v) (Y : I → C) (f : U ⟶ ∐ Y),
    ∃ Z : I → C, (∀ i, S (Z i)) ∧
      ∃ (a : ∀ i, Z i ⟶ Y i) (g : U ⟶ ∐ Z), g ≫ Limits.Sigma.map a = f

/-- Membership in the maximal class of alpha-small objects satisfying (G4).
The union of all such classes is expressed by this existential predicate.
Source: Krause (2001), page 122, definition of alpha-compactness.
(blueprint: def-sfb-alpha-compact-object) -/
def IsAlphaCompact (U : C) (α : Cardinal.{v}) : Prop :=
  ∃ S : ObjectProperty C, S U ∧
    (∀ V, S V → IsAlphaSmall V α) ∧ S.IsCoproductFactorizationClass

/-- The canonical object property of alpha-compact objects.
Source: Krause (2001), page 122, the subcategory denoted by T^alpha.
(blueprint: def-sfb-alpha-compact-object) -/
def alphaCompactObjects (C : Type u) [Category.{v} C] [HasCoproducts.{v} C]
    (α : Cardinal.{v}) : ObjectProperty C := fun U ↦ IsAlphaCompact U α

end CategoryTheory
