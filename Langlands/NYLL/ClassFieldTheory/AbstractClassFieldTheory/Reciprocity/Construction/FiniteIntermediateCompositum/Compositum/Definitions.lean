/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Definitions

/-!
# The compositum of two finite intermediate fields

Modified by Worker 5264, 15 November 2026: extract the definition M034.001
`FiniteIntermediateField.compositum` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source import by a focused published import,
and omit the rest of the source file. In the proof of the field `finite`, the
application of the unpublished theorem M033.014
`compositumWith_finite_over_base` is replaced by its source proof written
inline; in it the rewrite with `mem_extensionSubgroup_iff` (M022.001, whose
published form has a Prop-valued `Statement` type that `rw` cannot use) is
replaced by a rewrite with Mathlib's `Subgroup.mem_subgroupOf`. The
binders, docstring and data are unchanged. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The compositum of two finite intermediate fields of `E / K`. -/
def compositum {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    FiniteIntermediateField E K where
  field := M.field ⊓ N.field
  above := fun x hx => ⟨M.above hx, N.above hx⟩
  below := (inf_le_left :
    (M.field ⊓ N.field).toSubgroup ≤ M.field.toSubgroup).trans M.below
  finite := by
    let : Finite
        (K.toSubgroup ⧸ extensionSubgroup K N.field N.below) := N.finite
    have hMindex : M.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
      rw [Subgroup.relIndex]
      exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
        (extensionSubgroup K M.field M.below) M.finite
    have hSindex : N.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
      rw [Subgroup.relIndex]
      exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
        (extensionSubgroup K N.field N.below) N.finite
    apply Nat.finite_of_card_ne_zero
    change (extensionSubgroup K (M.compositumWith N.field)
        ((show (M.compositumWith N.field).toSubgroup ≤ N.field.toSubgroup from
          inf_le_right).trans N.below)).index ≠ 0
    have hsub : extensionSubgroup K (M.compositumWith N.field)
        ((show (M.compositumWith N.field).toSubgroup ≤ N.field.toSubgroup from
          inf_le_right).trans N.below) =
        (M.field.toSubgroup ⊓ N.field.toSubgroup).subgroupOf K.toSubgroup := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      rfl
    rw [hsub]
    simpa only [Subgroup.relIndex] using
      Subgroup.relIndex_inf_ne_zero hMindex hSindex

end FiniteIntermediateField

end

end Langlands.NYLL.ClassFormation
