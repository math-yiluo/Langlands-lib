/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# Ambient fixed additive subgroup of an integral representation

Modified by Worker 232, 12 November 2026: extract M023.001 from
`Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean` at
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, replace the source's module imports by the Mathlib
representation and closed-subgroup modules and the published
`IntegralRepGroupType` alias, and omit the unused `open CyclicCohomology`.
The construction is unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Ambient coefficient elements fixed pointwise by a closed abstract field
subgroup. -/
def ambientFixedAddSubgroup (A : Rep ℤ G) (H : ClosedSubgroup G) :
    AddSubgroup A.V := by
  exact
    { carrier := {a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}
      zero_mem' := fun h => map_zero (A.ρ h.1)
      add_mem' := by
        intro a b ha hb h
        rw [map_add, ha h, hb h]
      neg_mem' := by
        intro a ha h
        rw [map_neg, ha h] }

end

end Langlands.NYLL.KummerTheory
