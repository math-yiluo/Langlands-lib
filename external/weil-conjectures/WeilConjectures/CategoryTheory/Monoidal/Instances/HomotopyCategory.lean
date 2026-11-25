/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal

/-!

# Shortcut instances for monoidal homotopy category

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]

noncomputable instance :
    MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ)) :=
  have (X₁ X₂ : GradedObject ℤ A) : X₁.HasTensor X₂ := inferInstance
  inferInstance
