/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# NYLL abstract reciprocity: restriction in the upper exact row

Modified by Worker 68, 13 November 2026: extract M075.005, lines 457–472 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with `Langlands.NYLL`,
use focused imports and expand the source abbreviation
`CyclicCohomology.extensionSubgroup K L h` to its defining Mathlib term
`L.toSubgroup.subgroupOf K.toSubgroup`. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Preserve the source hypothesis name `hMK`, which the construction does not use.
set_option linter.unusedVariables false in
/-- The restriction `G(L/K) → G(M/K)` in the upper row. -/
def abstractReciprocityRestriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) →*
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) := by
  apply QuotientGroup.map
    (L.toSubgroup.subgroupOf K.toSubgroup)
    (M.toSubgroup.subgroupOf K.toSubgroup)
    (MonoidHom.id K.toSubgroup)
  intro k hk
  exact hLM hk

end
end Langlands.NYLL.ClassFormation
