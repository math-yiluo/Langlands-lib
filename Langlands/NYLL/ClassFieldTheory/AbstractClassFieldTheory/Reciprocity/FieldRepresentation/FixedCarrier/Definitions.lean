/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions

/-!
# NYLL extension fixed representation carrier equivalence

Modified by Worker 196, 13 November 2026: extract M073.001 (FieldRepresentation.lean:35–57) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with `Langlands.NYLL`, use focused
imports and expand the extension-subgroup abbreviation to its exact Mathlib body.
See the paired Markdown for the full correspondence and all modifications, and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The invariant carrier in the descended quotient representation is the
actual fixed group `A_L`. -/
def extensionFixedRepresentationEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal) :
    (extensionFixedRepresentation A K L hLK hnormal).V ≃+
      ambientFixedAddSubgroup A L where
  toFun x := ⟨x.1, by
    intro l
    exact x.2 ⟨⟨l.1, hLK l.2⟩, l.2⟩⟩
  invFun a := ⟨a.1, by
    intro s
    let l : L.toSubgroup := ⟨s.1.1, s.2⟩
    change A.ρ s.1.1 a.1 = a.1
    exact a.2 l⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

end
end Langlands.NYLL.ClassFormation
