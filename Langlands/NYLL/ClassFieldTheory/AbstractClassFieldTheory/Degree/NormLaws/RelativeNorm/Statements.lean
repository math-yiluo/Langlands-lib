/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions

/-!
# Relative-norm invariance and tower transitivity: statement targets

Modified by Worker 96, 14 November 2026: extract the statements of M026.013
and M026.019 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published relative norm, normal-extension action
and finite-tower modules instead of the original imports, replace
`extensionSubgroup K L hLK` by its exact `Subgroup.subgroupOf` body, and
publish Prop-valued definitions with the `Statement` suffix. The source proofs
and the unused `open CyclicCohomology` and `open scoped BigOperators Pointwise`
are omitted. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target: for a finite Galois abstract extension, the relative norm is
invariant under the `G_K`-conjugacy action on `A_L`. -/
def relativeNorm_normalExtensionActionStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) : Prop :=
    relativeNorm A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
      relativeNorm A K L hLK a

namespace DegreeData.FiniteTower

variable (T : DegreeData.FiniteTower G)

/-- Target: relative norms are transitive along a finite tower.  All
containments and finite quotient witnesses are obtained from `T`. -/
def norm_trans_applyStatement (A : Rep ℤ G)
    (a : ambientFixedAddSubgroup A T.top) : Prop :=
    relativeNorm A T.base T.middle T.middle_le_base
        (relativeNorm A T.middle T.top T.top_le_middle a) =
      relativeNorm A T.base T.top
        (T.top_le_middle.trans T.middle_le_base) a

end DegreeData.FiniteTower

end
end Langlands.NYLL.ClassFormation
