/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Essentially constant filtered diagrams

Source: Stacks Project, Categories, Definition 05PU
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe uJ vJ uC vC

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

/-- A filtered diagram `D` that is essentially constant with value `X`: natural maps
`p j : D.obj j ⟶ X`, a section `s : X ⟶ D.obj j₀` of `p j₀`, and for every `j` a common
later stage `k` at which the transition map from `j` factors through `p j`, `s` and `j₀ ⟶ k`.

Source: Stacks Project, Categories, Definition 05PU(1)
(auxiliary; not a blueprint node). -/
def IsEssentiallyConstantIndDiagram {J : Type uJ} {C : Type uC}
    [Category.{vJ} J] [Category.{vC} C] (D : J ⥤ C) (X : C) : Prop :=
  IsFiltered J ∧ ∃ p : D ⟶ (Functor.const J).obj X, ∃ j₀ : J, ∃ s : X ⟶ D.obj j₀,
    s ≫ p.app j₀ = 𝟙 X ∧
      ∀ j : J, ∃ k : J, ∃ a : j₀ ⟶ k, ∃ b : j ⟶ k,
        D.map b = p.app j ≫ s ≫ D.map a

end CategoryTheory
