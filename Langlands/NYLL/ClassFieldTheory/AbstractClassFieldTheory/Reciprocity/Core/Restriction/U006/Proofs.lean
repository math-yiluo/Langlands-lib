/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 9, 13 November 2026 UTC:
Extract only the proof of M075.006 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Core.Restriction.Statements
module. State the theorem as the published Statement applied to the source
parameters, whose normality instances use the expanded Mathlib form
L.toSubgroup.subgroupOf K.toSubgroup of the source extensionSubgroup
abbreviation. Retain the original proof rfl. Omit the source @[simp]
attribute, since the theorem's type is the Statement rather than a bare
equation, and the section variable {G : IntegralRepGroupType}, which the
source binder {G : Type*} shadows. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Statements

/-!
# Restriction in the upper exact row on quotient representatives

The exact proof that the restriction `G(L/K) → G(M/K)` sends the class of
`k : K` modulo `L` to the class of `k` modulo `M`.
-/

namespace Langlands.NYLL.ClassFormation

/--
Establishes the identity `abstractReciprocityRestriction K M L hLM hMK (QuotientGroup.mk k) =
QuotientGroup.mk k`.
-/
theorem abstractReciprocityRestriction_mk
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    abstractReciprocityRestriction_mkStatement K M L hLM hMK k :=
  rfl

end Langlands.NYLL.ClassFormation
