/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Directed

/-!
# Choosing a posetal subsystem that contains a fixed partial order

Source: the antisymmetrization construction, used to express Stacks Project, Sites,
Tag 00YO in terms of partially ordered indices
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w

namespace CategoryTheory

/-- A preorder has a cofinal posetal subsystem containing a given embedded partial order.
Source: antisymmetrization, with representatives fixed on the given partial order
(auxiliary; not a blueprint node). -/
theorem exists_pointSystem_posetal_replacement
    {J I : Type w} [PartialOrder J] [Preorder I]
    [Nonempty J] [IsDirected I (· ≤ ·)] (e : J ↪o I) :
    ∃ (M : Type w) (_ : PartialOrder M) (_ : Nonempty M) (_ : IsDirectedOrder M)
      (r : M ↪o I) (d : J ↪o M),
      d.trans r = e ∧ ∀ i, ∃ m, i ≤ r m ∧ r m ≤ i := by
  classical
  let M := Antisymmetrization I (· ≤ ·)
  let q : I → M := toAntisymmetrization (· ≤ ·)
  let d : J ↪o M :=
    { toFun := fun j ↦ q (e j)
      inj' := by
        intro j k h
        apply le_antisymm
        · apply e.le_iff_le.mp
          exact toAntisymmetrization_le_toAntisymmetrization_iff.mp h.le
        · apply e.le_iff_le.mp
          exact toAntisymmetrization_le_toAntisymmetrization_iff.mp h.ge
      map_rel_iff' := by
        intro j k
        exact toAntisymmetrization_le_toAntisymmetrization_iff.trans e.le_iff_le }
  let r : M → I := Function.extend d e (ofAntisymmetrization (· ≤ ·))
  have hr (m : M) : q (r m) = m := by
    by_cases hm : ∃ j, d j = m
    · obtain ⟨j, rfl⟩ := hm
      rw [show r (d j) = e j from d.injective.extend_apply _ _ j]
      rfl
    · rw [show r m = ofAntisymmetrization (· ≤ ·) m from
        Function.extend_apply' _ _ _ hm]
      exact toAntisymmetrization_ofAntisymmetrization (α := I) (r := (· ≤ ·)) m
  let re : M ↪o I :=
    { toFun := r
      inj' := by
        intro m n h
        rw [← hr m, ← hr n, h]
      map_rel_iff' := by
        intro m n
        have hh : q (r m) ≤ q (r n) ↔ r m ≤ r n :=
          toAntisymmetrization_le_toAntisymmetrization_iff
        rw [hr, hr] at hh
        exact hh.symm }
  have : Nonempty M := ⟨d (Classical.arbitrary J)⟩
  have : IsDirectedOrder M := ⟨fun m n ↦ by
    obtain ⟨i, hmi, hni⟩ := directed_of (· ≤ ·) (r m) (r n)
    refine ⟨q i, ?_, ?_⟩
    · exact (hr m) ▸ (show q (r m) ≤ q i from toAntisymmetrization_mono hmi)
    · exact (hr n) ▸ (show q (r n) ≤ q i from toAntisymmetrization_mono hni)⟩
  refine ⟨M, inferInstance, inferInstance, inferInstance, re, d, ?_, ?_⟩
  · ext j
    exact d.injective.extend_apply _ _ j
  · intro i
    refine ⟨q i, ?_, ?_⟩
    · apply toAntisymmetrization_le_toAntisymmetrization_iff.mp
      exact (hr (q i)).ge
    · apply toAntisymmetrization_le_toAntisymmetrization_iff.mp
      exact (hr (q i)).le

end CategoryTheory
