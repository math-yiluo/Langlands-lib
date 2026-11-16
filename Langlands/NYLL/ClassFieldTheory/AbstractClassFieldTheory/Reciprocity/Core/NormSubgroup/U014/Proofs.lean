/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.NormSubgroup.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.U019.Proofs

/-!
# NYLL M075.014: comparison of finite norm subgroups in a tower

Modified by Worker 735, 16 November 2026: extract the theorem
`abstractReciprocity_finiteNormSubgroup_le` (M075.014) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published statement module and the published
proof of `DegreeData.FiniteTower.norm_trans_apply` (M026.019) instead of the
source import, state the theorem through the published
`abstractReciprocity_finiteNormSubgroup_leStatement` with its finiteness
binders written, as in that statement, through the `Subgroup.subgroupOf`
bodies of the source's `extensionSubgroup` quotients, and open the proof with
a `show` of the unfolded statement. The source proof steps are retained
unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Norm transitivity identifies the norm image from `L` with a subgroup
of the norm image from `M`. -/
theorem abstractReciprocity_finiteNormSubgroup_le
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hKMfinite : Finite
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)]
    [hMLfinite : Finite
      (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup)]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    abstractReciprocity_finiteNormSubgroup_leStatement A K M L hLM hMK := by
  show finiteNormSubgroup A K L (hLM.trans hMK) ≤
      finiteNormSubgroup A K M hMK
  let T : DegreeData.FiniteTower G :=
    { top := L
      middle := M
      base := K
      top_le_middle := hLM
      middle_le_base := hMK
      finiteTopQuotient := hMLfinite
      finiteBaseQuotient := hKMfinite }
  rintro _ ⟨a, rfl⟩
  refine ⟨relativeNorm A M L hLM a, ?_⟩
  exact T.norm_trans_apply A a

end
end Langlands.NYLL.ClassFormation
