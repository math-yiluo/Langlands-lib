/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# Relative norm evaluation statement target

Modified by Worker 96, 14 November 2026: extract the statement of M024.010
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published relative norm, replace
`extensionSubgroup K L hLK` by its exact `Subgroup.subgroupOf` body, and
publish a Prop-valued definition with the `Statement` suffix.
The source proof and simp attribute are omitted.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes `G` to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target: coercing a relative norm gives the explicit sum over quotient
representatives. -/
def relativeNorm_apply_coeStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A L) : Prop :=
    ((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
      relativeNormValue A K L hLK a

end
end Langlands.NYLL.ClassFormation
