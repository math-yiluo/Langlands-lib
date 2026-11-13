/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions

/-!
# NYLL positive representatives and extension restriction targets

Modified by Worker 191: extract M012.001 and .008 as Prop-valued Statement
definitions; prefix the namespace with Langlands.NYLL and expand the
extensionSubgroup abbreviation to its exact Mathlib body. Preserve all
source universes, binders and conclusions. Omit theorem proofs and the
theorem-only simp attribute, and use the focused data import.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Target: every class of a finite-index subgroup of `ℤ̂` has a strictly
positive natural multiple of `1` as a representative. -/
def exists_positive_nsmul_one_sub_mem_of_index_ne_zeroStatement
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) (z : ZHat) : Prop :=
  ∃ n : ℕ, 0 < n ∧ z - n • (1 : ZHat) ∈ H

namespace DegreeData

/-- Target for evaluation of extension restriction on a quotient representative. -/
def extensionRestriction_mkStatement (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) : Prop :=
  D.extensionRestriction K L hLK (QuotientGroup.mk k) =
    QuotientGroup.mk k

end DegreeData

end
end Langlands.NYLL.ClassFormation
