/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Statements

/-!
# NYLL M039.012: vanishing of a finite norm class

Modified by Worker 520, 16 November 2026: extract M039.012 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, import the published statement module, expand
`extensionSubgroup` to its `Subgroup.subgroupOf` body, and state the theorem
through the published `finiteNormClass_eq_zero_iffStatement`. A leading `show`
unfolds that target; the remaining proof and the `simp` attribute are the source's.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- A finite norm class vanishes exactly when its representative is a norm. -/
@[simp]
theorem finiteNormClass_eq_zero_iff
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A K) :
    finiteNormClass_eq_zero_iffStatement A K L hLK a := by
  show finiteNormClass A K L hLK a = 0 ↔ a ∈ finiteNormSubgroup A K L hLK
  unfold finiteNormClass finiteNormClassHom FiniteNormQuotient
  exact QuotientAddGroup.eq_zero_iff _

end
end Langlands.NYLL.ClassFormation
