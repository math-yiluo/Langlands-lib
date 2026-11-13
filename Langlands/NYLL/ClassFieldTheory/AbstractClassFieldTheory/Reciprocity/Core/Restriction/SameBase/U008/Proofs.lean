/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.SameBase.Statements

/-!
# NYLL same-base naturality restriction agrees with reciprocity restriction

Modified by Worker 190, 13 November 2026: extract the proof of M075.008 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean:509–523`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, import the published statement and prove that exact target.
Expand the source extension-subgroup abbreviation to its Mathlib body in the
normality binders. Retain the original extensionality and quotient-induction
proof. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` for attribution and the modification record.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

set_option linter.unusedVariables false in
/-- With equal base subgroups, the naturality restriction is the restriction
in the upper row of the abstract reciprocity reduction. -/
theorem finiteReciprocityNaturalityRestriction_sameBase_eq_restriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    finiteReciprocityNaturalityRestriction_sameBase_eq_restrictionStatement
      K M L hLM hMK := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  rfl

end
end Langlands.NYLL.ClassFormation
