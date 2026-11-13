/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 9, 13 November 2026 UTC:
Extract only the proof of M071.003 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published
MainTransfer.Intermediate.Statements module. State the theorem as the
published Statement applied to the source parameters. Replace each
occurrence of the source abbreviation extensionSubgroup X Y h by its
Mathlib body Y.toSubgroup.subgroupOf X.toSubgroup, and each use of
KummerTheory.mem_extensionSubgroup_iff X Y h x (whose source proof is
Iff.rfl) by Mathlib's Subgroup.mem_subgroupOf with its arguments left
implicit. The proof is otherwise the original one line for line. Keep the
source universe u and section variables {G : Type u} [Group G]
[TopologicalSpace G]. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.Intermediate.Statements

/-!
# Injectivity of the intermediate quotient inclusion

The exact proof that the inclusion `G(L/K') → G(L/K)` induced by `K' ≤ K`
is injective.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The inclusion of finite Galois groups attached to an intermediate field
is injective. -/
theorem transferNormNaturalityIntermediateInclusion_injective
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    transferNormNaturalityIntermediateInclusion_injectiveStatement K K' L hLK' hK'K := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  apply Subgroup.mem_subgroupOf.2
  have hmem :
      (Subgroup.inclusion hK'K k')⁻¹ *
          Subgroup.inclusion hK'K l' ∈
        L.toSubgroup.subgroupOf K.toSubgroup :=
    QuotientGroup.eq.mp h
  have hG := Subgroup.mem_subgroupOf.1 hmem
  simpa using hG

end Langlands.NYLL.ClassFormation
