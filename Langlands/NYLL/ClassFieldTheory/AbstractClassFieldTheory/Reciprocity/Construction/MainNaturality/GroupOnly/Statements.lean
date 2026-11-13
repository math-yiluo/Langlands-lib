/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# NYLL naturality composite-quotient finiteness target

Modified by Worker 196, 13 November 2026: extract M066.013, lines 405–412 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean` at `fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with
`Langlands.NYLL`, use focused imports and turn source theorems into Prop-valued
definitions without their proofs. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

def _root_.Langlands.NYLL.PortInternal.M066.d013Statement
    (K K' L' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [Finite (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)]
    [Finite (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)] : Prop :=
    Finite (K.toSubgroup ⧸
      L'.toSubgroup.subgroupOf K.toSubgroup)

end
end Langlands.NYLL.ClassFormation
