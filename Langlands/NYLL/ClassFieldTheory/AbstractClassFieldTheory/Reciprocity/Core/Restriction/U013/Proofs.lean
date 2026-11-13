/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 9, 13 November 2026 UTC:
Extract only the proof of M075.013 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Core.Restriction.Statements
module. State the theorem as the published Statement applied to the source
parameters. Replace each occurrence of the source abbreviation
extensionSubgroup X Y h by its Mathlib body Y.toSubgroup.subgroupOf
X.toSubgroup, and each use of KummerTheory.mem_extensionSubgroup_iff X Y h x
(whose source proof is Iff.rfl) by Mathlib's Subgroup.mem_subgroupOf with
its arguments left implicit. The proof is otherwise the original one line
for line. Omit the section variable {G : IntegralRepGroupType}, which the
source binder {G : Type*} shadows. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Statements

/-!
# Finiteness of the lower extension

The exact proof that finiteness of `G(L/K)` implies finiteness of `G(L/M)`,
by an injection of left-coset types.
-/

namespace Langlands.NYLL.ClassFormation

/-- Finiteness of `L | K` also implies finiteness of `L | M`. -/
theorem abstractReciprocity_lowerExtension_finite
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    abstractReciprocity_lowerExtension_finiteStatement K M L hLM hMK := by
  let inclusion :
      (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) →
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
    Quotient.map' (Subgroup.inclusion hMK) (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      apply Subgroup.mem_subgroupOf.2
      simpa using Subgroup.mem_subgroupOf.1 hxy)
  apply Finite.of_injective inclusion
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro m
  refine QuotientGroup.induction_on y ?_
  intro n h
  apply QuotientGroup.eq.mpr
  apply Subgroup.mem_subgroupOf.2
  have h' :
      (QuotientGroup.mk (Subgroup.inclusion hMK m) :
          K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) =
        QuotientGroup.mk (Subgroup.inclusion hMK n) := by
    simpa [inclusion] using h
  have hmem := QuotientGroup.eq.mp h'
  have hG := Subgroup.mem_subgroupOf.1 hmem
  simpa using hG

end Langlands.NYLL.ClassFormation
