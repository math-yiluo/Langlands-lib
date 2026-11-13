/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# NYLL finite reciprocity naturality restriction

Modified by Worker 196, 13 November 2026: extract M066.001, lines 42–59 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean` at `fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with
`Langlands.NYLL`, use focused imports and turn source theorems into Prop-valued
definitions without their proofs. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

def finiteReciprocityNaturalityRestriction
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup) →*
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := by
  apply QuotientGroup.map
    (L'.toSubgroup.subgroupOf K'.toSubgroup)
    (L.toSubgroup.subgroupOf K.toSubgroup)
    (Subgroup.inclusion hK'K)
  intro k' hk'L'
  change k'.1 ∈ L'.toSubgroup at hk'L'
  change (Subgroup.inclusion hK'K k').1 ∈ L.toSubgroup
  exact hL'L hk'L'

end
end Langlands.NYLL.ClassFormation
