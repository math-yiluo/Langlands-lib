/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.Restriction.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions

/-!
# NYLL abstract reciprocity: same-base naturality restriction target

Modified by Worker 68, 13 November 2026: extract the asserted type of M075.008, lines 509–519
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709` as a Prop-valued definition without its proof.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to the theorem name, use
focused imports and expand the source abbreviation `CyclicCohomology.extensionSubgroup K L h`
to its defining Mathlib term `L.toSubgroup.subgroupOf K.toSubgroup`. See the paired Markdown
for all changes and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained
attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Preserve the source instance names, which the conclusion does not mention by name.
set_option linter.unusedVariables false in
/-- Target of `finiteReciprocityNaturalityRestriction_sameBase_eq_restriction`: with equal
base fields, the Galois-side restriction of norm–conjugation naturality is the restriction
in the upper exact row of the reciprocity reduction. -/
def finiteReciprocityNaturalityRestriction_sameBase_eq_restrictionStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] : Prop :=
    finiteReciprocityNaturalityRestriction K K M L hMK (hLM.trans hMK) le_rfl hLM =
      abstractReciprocityRestriction K M L hLM hMK

end
end Langlands.NYLL.ClassFormation
