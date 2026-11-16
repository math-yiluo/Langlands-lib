/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Statements

/-!
# NYLL M039.010: finite norm classes commute with natural scalar multiplication

Modified by Worker 520, 16 November 2026: extract M039.010 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, import the published statement module, expand
`extensionSubgroup` to its `Subgroup.subgroupOf` body, and state the theorem
through the published `finiteNormClass_nsmulStatement`.
The proof and the `simp` attribute are unchanged.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Finite norm classes commute with natural scalar multiplication. -/
@[simp]
theorem finiteNormClass_nsmul
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (n : ℕ) (a : ambientFixedAddSubgroup A K) :
    finiteNormClass_nsmulStatement A K L hLK n a := by
  exact map_nsmul (finiteNormClassHom A K L hLK) n a

end
end Langlands.NYLL.ClassFormation
