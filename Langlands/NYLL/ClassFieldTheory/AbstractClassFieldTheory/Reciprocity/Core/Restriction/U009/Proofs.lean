/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 9, 13 November 2026 UTC:
Extract only the proof of M075.009 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Core.Restriction.Statements
module. State the theorem as the published Statement applied to the source
parameters, whose instances use the expanded Mathlib form
L.toSubgroup.subgroupOf K.toSubgroup of the source extensionSubgroup
abbreviation. Retain the original Finite.of_surjective step along the
restriction map, but supply its surjectivity argument inline by the
original four-line proof of M075.007 (Core.lean lines 502-505) instead of
citing abstractReciprocityRestriction_surjective, which is not yet in the
Library. Omit the section variable {G : IntegralRepGroupType}, which the
source binder {G : Type*} shadows. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Statements

/-!
# Finiteness of the intermediate quotient

The exact proof that finiteness of `G(L/K)` implies finiteness of `G(M/K)`,
derived from the surjective restriction map.
-/

namespace Langlands.NYLL.ClassFormation

/-- Finiteness of `L | K` implies finiteness of the quotient `G(M/K)`.
This is derived from the actual surjective restriction map. -/
theorem abstractReciprocity_intermediateQuotient_finite
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    abstractReciprocity_intermediateQuotient_finiteStatement K M L hLM hMK :=
  Finite.of_surjective (abstractReciprocityRestriction K M L hLM hMK) (by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro k
    exact ⟨QuotientGroup.mk k, rfl⟩)

end Langlands.NYLL.ClassFormation
