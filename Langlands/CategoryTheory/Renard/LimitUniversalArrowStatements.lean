import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Langlands.CategoryTheory.Renard.ConeBridge

/-!
# Renard A.IV.1–2: limits and colimits as universal arrows for the diagonal

These closed propositions identify a limit (colimit) of a diagram `D` with a
left (right) universal arrow for the actual diagonal functor and `D`, both as
terminal (initial) structured-arrow data and as the unique factorization
property of A.III.1. This file supplies statements only.
-/

open CategoryTheory CategoryTheory.Limits

universe vJ vC uJ uC

namespace Langlands.Renard.LimitUniversalArrow

open Langlands.CategoryTheory.Renard

/-- A cone `(X, η)` is limiting iff `η` is a terminal costructured arrow from the diagonal. -/
def LimitUniversalStatement : Prop :=
  ∀ (J : Type uJ) [Category.{vJ} J] (C : Type uC) [Category.{vC} C]
    (D : J ⥤ C) (X : C) (η : (diagonal J C).obj X ⟶ D),
    Nonempty (IsLimit (Cone.mk X η)) ↔
    Nonempty (CostructuredArrow.IsUniversal (CostructuredArrow.mk (S := diagonal J C) η))

/-- A cone `(X, η)` is limiting iff it solves the left universal problem posed by the
diagonal and `D`. -/
def LimitFactorizationStatement : Prop :=
  ∀ (J : Type uJ) [Category.{vJ} J] (C : Type uC) [Category.{vC} C]
    (D : J ⥤ C) (X : C) (η : (diagonal J C).obj X ⟶ D),
    Nonempty (IsLimit (Cone.mk X η)) ↔
    ∀ (Y : C) (f : (diagonal J C).obj Y ⟶ D),
      ∃! g : Y ⟶ X, (diagonal J C).map g ≫ η = f

/-- A cocone `(X, η)` is colimiting iff `η` is an initial structured arrow to the diagonal. -/
def ColimitUniversalStatement : Prop :=
  ∀ (J : Type uJ) [Category.{vJ} J] (C : Type uC) [Category.{vC} C]
    (D : J ⥤ C) (X : C) (η : D ⟶ (diagonal J C).obj X),
    Nonempty (IsColimit (Cocone.mk X η)) ↔
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk (T := diagonal J C) η))

/-- A cocone `(X, η)` is colimiting iff it solves the right universal problem posed by the
diagonal and `D`. -/
def ColimitFactorizationStatement : Prop :=
  ∀ (J : Type uJ) [Category.{vJ} J] (C : Type uC) [Category.{vC} C]
    (D : J ⥤ C) (X : C) (η : D ⟶ (diagonal J C).obj X),
    Nonempty (IsColimit (Cocone.mk X η)) ↔
    ∀ (Y : C) (f : D ⟶ (diagonal J C).obj Y),
      ∃! g : X ⟶ Y, η ≫ (diagonal J C).map g = f

/-- The four limit and colimit universal-arrow comparisons. -/
def LimitUniversalArrowStatements : Prop :=
  LimitUniversalStatement.{vJ, vC, uJ, uC} ∧
  LimitFactorizationStatement.{vJ, vC, uJ, uC} ∧
  ColimitUniversalStatement.{vJ, vC, uJ, uC} ∧
  ColimitFactorizationStatement.{vJ, vC, uJ, uC}

end Langlands.Renard.LimitUniversalArrow
