/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Essentially constant inverse systems of abelian groups

Source: Stacks Project, Categories, Definitions 4.22.1(2) and 4.22.2, Tags 05PU and 05PV
(blueprint: def-weil-pbc-essentially-constant-system).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.Functor

/-- An inverse system of abelian groups is essentially constant with value `X` when there are
compatible maps `π n : X ⟶ F.obj (op n)` which split at one index `i₀`. Every transition
map into `j` then eventually factors through `X` using that splitting. The index `n : ℕ`
represents the positive integer `n + 1` (Stacks, Tags 05PU(2), 05PV).
(blueprint: def-weil-pbc-essentially-constant-system) -/
def IsEssentiallyConstantWithValue (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (X : AddCommGrpCat.{u}) :
    Prop :=
  ∃ π : ∀ n : ℕ, X ⟶ F.obj (Opposite.op n),
    (∀ n : ℕ,
      π (n + 1) ≫ F.map (homOfLE (Nat.le_add_right n 1)).op = π n) ∧
    ∃ (i₀ : ℕ) (r : F.obj (Opposite.op i₀) ⟶ X),
      (π i₀ ≫ r = 𝟙 X) ∧
      ∀ j : ℕ, ∃ k : ℕ, ∃ (hik : i₀ ≤ k) (hjk : j ≤ k),
        F.map (homOfLE hjk).op =
          F.map (homOfLE hik).op ≫ r ≫ π j

/-- An inverse system of abelian groups is essentially constant when it is essentially constant
with some value `X` (`IsEssentiallyConstantWithValue`). The index `n : ℕ` represents the
positive integer `n + 1` (Stacks, Tags 05PU(2), 05PV).
(blueprint: def-weil-pbc-essentially-constant-system) -/
def IsEssentiallyConstant (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : Prop :=
  ∃ X : AddCommGrpCat.{u}, F.IsEssentiallyConstantWithValue X

end CategoryTheory.Functor
