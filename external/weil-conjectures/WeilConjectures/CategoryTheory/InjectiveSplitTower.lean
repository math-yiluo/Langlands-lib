/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.InjectiveSplitTowerExtension

/-!
# Injectivity of split towers of injective abelian groups

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1 proof footnote
(blueprint: lem-pc-injective-split-tower-injective).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

/-- A tower of injective abelian groups with split surjective transitions is injective in the
abelian category of towers (Stacks Project, Tag 07KW, Lemma 15.88.1 proof footnote).
The index `n : ℕ` denotes the paper's level `n + 1`.

To lift a morphism `A ⟶ I` along a monomorphism `A ⟶ B` of towers, use a tower with
`ℤ` through level `n` and zero above: maps from it to `A` correspond to elements of `A_n`.
This shows each component `A_n ⟶ B_n` is monic. Extend the map at level zero using
injectivity of `I_0`.

Given a compatible lift at level `n`, choose a section of `p_n : I_{n+1} ⟶ I_n`.
On `A_{n+1}`, subtract the section applied to the previous lift composed with the
transition of `B` from the given map to `I_{n+1}`. Compatibility makes this difference
land in `ker p_n`. The kernel is an injective direct summand of `I_{n+1}`, so extend
the difference to `B_{n+1}` and add back the section term. The resulting level maps
form a compatible tower morphism extending the original map.
(blueprint: lem-pc-injective-split-tower-injective) -/
theorem injective_of_injective_split_tower (I : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hI : ∀ n : ℕ, Injective (I.obj (Opposite.op n)))
    (hp : ∀ n : ℕ, IsSplitEpi (I.map (homOfLE (Nat.le_add_right n 1)).op)) :
    Injective I := by
  constructor
  intro A B g f inst
  exact injective_split_tower_extension I hI hp f g

end CategoryTheory
