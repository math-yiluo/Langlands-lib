/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 9, 13 November 2026 UTC:
Extract only the proof of M075.007 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Core.Restriction.Statements
module. State the theorem as the published Statement applied to the source
parameters, whose normality instances use the expanded Mathlib form
L.toSubgroup.subgroupOf K.toSubgroup of the source extensionSubgroup
abbreviation. Retain the original four-line tactic proof verbatim; its
initial intro unfolds the Statement. Omit the section variable
{G : IntegralRepGroupType}, which the source binder {G : Type*} shadows.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Statements

/-!
# Surjectivity of restriction in the upper exact row

The exact proof that the restriction `G(L/K) → G(M/K)` is surjective.
-/

namespace Langlands.NYLL.ClassFormation

/-- Restriction to the intermediate Galois extension is surjective. -/
theorem abstractReciprocityRestriction_surjective
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    abstractReciprocityRestriction_surjectiveStatement K M L hLM hMK := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  exact ⟨QuotientGroup.mk k, rfl⟩

end Langlands.NYLL.ClassFormation
