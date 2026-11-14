/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions

/-!
# The finite norm quotient: the maximal-unramified norm subgroup targets

Modified by Worker 96, 14 November 2026: extract the statements of
M039.019 and M039.020 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published finite norm quotient data and the
published maximal-unramified norm subgroup, replace
`extensionSubgroup K L hLK` by its exact `Subgroup.subgroupOf` body, and
publish Prop-valued definitions whose binders are the source hypotheses in
source order. The public theorem M039.019 receives the `Statement` suffix;
the private theorem M039.020 receives the name
`Langlands.NYLL.PortInternal.M039.d020Statement`. The source proofs are
omitted. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

section quotientMaps

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the defining intersection for the infinite norm subgroup is
contained in the norm image from the particular finite field `L`. -/
def maximalUnramifiedNormSubgroup_le_finiteNormSubgroupStatement
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    Prop :=
    D.maximalUnramifiedNormSubgroup A K L ≤
      finiteNormSubgroup A K L hLK

/-- Target for the private source theorem
`DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker`: the
maximal-unramified norm subgroup lies in the kernel of the finite norm class
map. -/
def _root_.Langlands.NYLL.PortInternal.M039.d020Statement
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    Prop :=
    D.maximalUnramifiedNormSubgroup A K L ≤
      (finiteNormClassHom A K L hLK).ker

end DegreeData

end quotientMaps

end
end Langlands.NYLL.ClassFormation
