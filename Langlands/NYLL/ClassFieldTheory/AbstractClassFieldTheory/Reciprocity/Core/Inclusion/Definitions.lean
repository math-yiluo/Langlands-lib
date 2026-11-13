/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.Intermediate.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry.GroupOnly.U003.Proofs

/-!
# NYLL abstract reciprocity: inclusion in the upper exact row

Modified by Worker 68, 13 November 2026: extract M075.010, lines 543–556 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with `Langlands.NYLL`,
use focused imports and expand the source abbreviation
`CyclicCohomology.extensionSubgroup K L h` to its defining Mathlib term
`L.toSubgroup.subgroupOf K.toSubgroup`. The two `letI` binders still cite the theorem
`transferNormNaturality_intermediateExtension_normal` (M068.003), now its published
Library proof. See the paired Markdown for all changes and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- The inclusion `G(L/M) → G(L/K)` in the upper row.
Normality of `L | M` is derived from normality of `L | K`. -/
def abstractReciprocityInclusion
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) →*
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := by
  letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  exact transferNormNaturalityIntermediateInclusion K M L hLM hMK

end
end Langlands.NYLL.ClassFormation
