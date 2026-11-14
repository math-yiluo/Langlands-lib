/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions

/-!
# NYLL abstract reciprocity: comparison of finite norm subgroups in a tower

Modified by Worker 68, 14 November 2026: extract the asserted type of M075.014, lines
656–667 from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709` as a Prop-valued definition without its proof.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to the theorem name, use a
focused import of the published finite norm subgroup (M039.001) and expand the source
abbreviation `CyclicCohomology.extensionSubgroup K L h` to its defining Mathlib term
`L.toSubgroup.subgroupOf K.toSubgroup`. The unused-variables linter is disabled for this
declaration only, so the source instance name `hMLfinite` (used only by the omitted
proof) is kept. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

set_option linter.unusedVariables false in
/-- Target of `abstractReciprocity_finiteNormSubgroup_le`: norm transitivity identifies the
norm image from `L` with a subgroup of the norm image from `M`. -/
def abstractReciprocity_finiteNormSubgroup_leStatement
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hKMfinite : Finite
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)]
    [hMLfinite : Finite
      (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup)]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] : Prop :=
    finiteNormSubgroup A K L (hLM.trans hMK) ≤
      finiteNormSubgroup A K M hMK

end
end Langlands.NYLL.ClassFormation
