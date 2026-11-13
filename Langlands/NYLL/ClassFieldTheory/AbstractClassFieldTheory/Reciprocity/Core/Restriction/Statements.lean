/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions

/-!
# NYLL abstract reciprocity: restriction and finiteness targets

Modified by Worker 68, 13 November 2026: extract the asserted types of M075.006, lines
479–489; M075.007, lines 493–501; M075.009, lines 527–537; and M075.013, lines 620–627 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709` as Prop-valued definitions without their proofs.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to each theorem name, use
focused imports and expand the source abbreviation `CyclicCohomology.extensionSubgroup K L h`
to its defining Mathlib term `L.toSubgroup.subgroupOf K.toSubgroup`. See the paired Markdown
for all changes and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained
attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Preserve the source hypothesis and instance names even when the conclusions do not
-- mention them.
set_option linter.unusedVariables false in
/--
Target of `abstractReciprocityRestriction_mk`: the restriction sends the class of `k` to the
class of `k`.
-/
def abstractReciprocityRestriction_mkStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) : Prop :=
    abstractReciprocityRestriction K M L hLM hMK (QuotientGroup.mk k) =
      QuotientGroup.mk k

set_option linter.unusedVariables false in
/-- Target of `abstractReciprocityRestriction_surjective`: restriction to the intermediate
Galois extension is surjective. -/
def abstractReciprocityRestriction_surjectiveStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] : Prop :=
    Function.Surjective (abstractReciprocityRestriction K M L hLM hMK)

set_option linter.unusedVariables false in
/-- Target of `abstractReciprocity_intermediateQuotient_finite`: finiteness of `L | K`
implies finiteness of the quotient `G(M/K)`. -/
def abstractReciprocity_intermediateQuotient_finiteStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] : Prop :=
    Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)

set_option linter.unusedVariables false in
/-- Target of `abstractReciprocity_lowerExtension_finite`: finiteness of `L | K` also
implies finiteness of `L | M`. -/
def abstractReciprocity_lowerExtension_finiteStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] : Prop :=
    Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup)

end
end Langlands.NYLL.ClassFormation
