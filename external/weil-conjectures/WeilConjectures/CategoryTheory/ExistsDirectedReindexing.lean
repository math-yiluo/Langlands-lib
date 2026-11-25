/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final

/-!
# One directed reindexing for colimits and inverse limits

Source: Stacks Project, Categories, Lemma 4.21.5 (Tag 0032), clauses (1) and (2)
(blueprint: lem-weil-pbc-filtered-category-directed-cofinal).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- A small filtered category has a single nonempty directed reindexing preserving all given
colimit cocones and all given limit cones on opposite diagrams. The functor `F` encodes the
objects `x_a` and transition maps `φ_ab`; its identity and composition laws are precisely the
system laws. Whiskering retains the given vertex and selects its legs at `F.obj a`.
Source: Stacks Project, Categories, Lemma 4.21.5 (Tag 0032), clauses (1) and (2)
(blueprint: lem-weil-pbc-filtered-category-directed-cofinal).

Proof:
1. Apply `lem-weil-pbc-filtered-category-exists-directed-final` to obtain a nonempty directed
   index and a final functor `F`. Its object and arrow maps give the required system, with both
   laws supplied by functoriality, independently of the target category and diagram.
2. For `F.op`, the nonemptiness condition in
   `lem-weil-pbc-initial-functor-cofiltered-criterion` is finality's first condition. For its
   equalization condition, push the finite zigzag in finality's second condition to a common
   upper bound in the directed index. Functoriality makes all resulting arrows equal.
   Apply that criterion with the target indexing category `Jᵒᵖ`: the canonical colimit map is
   an isomorphism, so the restricted cocone with the original vertex is a colimit.
3. The same `F.op` satisfies `lem-weil-pbc-initial-functor-limit`: nonemptiness is as above,
   and inserting identities at the ends of the finality zigzag gives the required orientation.
   Its clause (a) makes the restricted cone a limit, with the same index and functor.
-/
theorem exists_directed_reindexing (J : Type w) [SmallCategory J] [IsFiltered J] :
    ∃ (A : Type w) (_ : Preorder A) (_ : IsDirected A (· ≤ ·)) (_ : Nonempty A)
      (F : A ⥤ J),
      ∀ (C : Type u) (_ : Category.{v} C),
        (∀ (M : J ⥤ C) (c : Cocone M),
          IsColimit c → Nonempty (IsColimit (c.whisker F))) ∧
        (∀ (M : Jᵒᵖ ⥤ C) (c : Cone M),
          IsLimit c → Nonempty (IsLimit (c.whisker F.op))) := by
  obtain ⟨A, horder, hdirected, hnonempty, F, hfinal⟩ := IsFiltered.exists_directed J
  let :=  horder
  let :=  hfinal
  refine ⟨A, horder.toPreorder, hdirected, hnonempty, F, ?_⟩
  intro C hC
  constructor
  · intro M c hc
    exact ⟨(Functor.Final.isColimitWhiskerEquiv F c).symm hc⟩
  · intro M c hc
    exact ⟨(Functor.Initial.isLimitWhiskerEquiv F.op c).symm hc⟩

end CategoryTheory
