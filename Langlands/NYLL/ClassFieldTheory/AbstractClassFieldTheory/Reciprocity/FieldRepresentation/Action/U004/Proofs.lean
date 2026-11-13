/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.Statements

/-!
# NYLL fixed representation and relative coset action agree

Modified by Worker 190, 13 November 2026: extract M073.004 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean:87–100`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, import the published statement and prove that exact target.
Expand the extension-subgroup abbreviation to its defining Mathlib term.
After quotient induction, use definitional reduction directly in place of
rewriting by the source's reflexive `relativeCosetAction_mk` lemma.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` for attribution and the modification record.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The quotient representation action on fixed vectors agrees with the
relative coset action after coercion to the ambient representation. -/
theorem extensionFixedRepresentation_action_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    extensionFixedRepresentation_action_coeStatement A K L hLK hnormal q a := by
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro k
  rfl

end
end Langlands.NYLL.ClassFormation
