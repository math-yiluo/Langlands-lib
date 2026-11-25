/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Replete topoi of set-valued sheaves

Source: blueprint `definition-repleteness--1` (chap-The-pro-etale-site, definition-repleteness);
Bhatt–Scholze, *The pro-étale topology*, Definition 3.1.1.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology

/-- A Grothendieck topology `J` is *replete* (blueprint: definition-repleteness--1;
Bhatt–Scholze, Definition 3.1.1) when, in the topos of set-valued sheaves on `J`, every
inverse sequence of epimorphisms has epimorphic projections from its limit, at every index.
An inverse sequence is `F : ℕᵒᵖ ⥤ Sheaf J (Type (max u v w))`; its adjacent transition
is `F.map (homOfLE (Nat.le_succ n)).op`.

The existing sectionwise-limit construction (`Sheaf.createsLimitsOfShape`, Stacks 00W2)
identifies `limit F` at `V` with the tuples `x n ∈ (F.obj (op n))(V)` satisfying
`t_n (x (n + 1)) = x n`; `limit.π F (op m)` is the coordinate projection `x ↦ x m`.
By `Sheaf.isLocallySurjective_iff_epi` (Stacks 00WM and 00WN), epimorphism here means
that each target section admits lifts after passing to a covering. Thus neither the
transition hypothesis nor the projection conclusion asserts surjectivity on all sections.
The extra universe `w` allows section sets larger than the site. -/
def IsReplete {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) : Prop :=
  ∀ (F : ℕᵒᵖ ⥤ Sheaf J (Type (max u v w))),
    (∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) →
      ∀ m : ℕ, Epi (limit.π F (op m))

end CategoryTheory.GrothendieckTopology
