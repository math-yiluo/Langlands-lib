/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones

/-! # Essentially constant cofiltered diagrams

Source: Stacks Project, Categories, Definition 05PU
(blueprint: def-pc-essentially-constant-pro-diagram).
-/

@[expose] public section

universe uJp vJp uCp vCp

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

/-- A cofiltered diagram `D` that is essentially constant with value `X` as a pro-object:
natural maps `u j : X ⟶ D.obj j`, a retraction `r : D.obj j₀ ⟶ X` of `u j₀`, and for every
`j` a common earlier stage `k` at which the transition map to `j` factors through
`k ⟶ j₀`, `r` and `u j`.

Source: Stacks Project, Categories, Definition 05PU(2)
(blueprint: def-pc-essentially-constant-pro-diagram). -/
def IsEssentiallyConstantProDiagram {J : Type uJp} {C : Type uCp}
    [Category.{vJp} J] [Category.{vCp} C] (D : J ⥤ C) (X : C) : Prop :=
  IsCofiltered J ∧ ∃ u : (Functor.const J).obj X ⟶ D, ∃ j₀ : J, ∃ r : D.obj j₀ ⟶ X,
    u.app j₀ ≫ r = 𝟙 X ∧
      ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
        D.map b = D.map a ≫ r ≫ u.app j

end CategoryTheory
