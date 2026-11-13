/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Inclusion.Definitions

/-!
# NYLL abstract reciprocity: exactness of the upper Galois row

Modified by Worker 68, 13 November 2026: extract the asserted type of M075.012, lines
581–592 from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709` as a Prop-valued definition without its proof.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to the theorem name, use
focused imports and expand the source abbreviation
`CyclicCohomology.extensionSubgroup K L h` to its defining Mathlib term
`L.toSubgroup.subgroupOf K.toSubgroup`. The `letI` binder still cites the theorem
`transferNormNaturality_intermediateExtension_normal` (M068.003), now its published
Library proof. See the paired Markdown for all changes and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Target of `abstractReciprocity_galois_exact`: the upper row is exact at `G(L/K)`; the
image of `G(L/M)` is exactly the kernel of restriction to `G(M/K)`. -/
def abstractReciprocity_galois_exactStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] : Prop :=
    letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    (abstractReciprocityRestriction K M L hLM hMK).ker =
      (abstractReciprocityInclusion K M L hLM hMK).range

end
end Langlands.NYLL.ClassFormation
