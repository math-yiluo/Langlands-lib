/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 754 (2026-11-16): extract only the proof of M016.015
`frobeniusFixedSubgroupWithin_normalizedDegree_image` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean
(lines 324–353) at commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace ClassFormation with Langlands.NYLL; import only the published
ResidueDegree Statements module and state the theorem as its
`frobeniusFixedSubgroupWithin_normalizedDegree_imageStatement` applied to the
source binders, with `extensionSubgroup K.field L hLK` expanded to its Mathlib
body `L.toSubgroup.subgroupOf K.field.toSubgroup` as in that statement. In the
proof, the source application `(D.extensionNormalizedDegree_mk K L hLK k).symm`
of the then unpublished theorem M012.006 is replaced by `rfl`, the source proof
of M012.006; the rest of the tactic proof is unchanged. The unused
`open CyclicCohomology` is omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.ResidueDegree.Statements

/-!
# The normalized-degree image of the Frobenius fixed subgroup (NYLL M016.015)

The image of `G_Σ ≤ G_K` under the normalized degree of `K` equals the range
of the normalized degree on the closed cyclic subgroup `Γ = closure ⟨σ⟩` of
`G_K / I_L`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The normalized-degree image of the actual subgroup `G_Σ ≤ G_K` is
the image already computed on the group-dual `Γ`. -/
theorem frobeniusFixedSubgroupWithin_normalizedDegree_image
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusFixedSubgroupWithin_normalizedDegree_imageStatement K L hLK σ := by
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨QuotientGroup.mk k, hk⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) a.1
    have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
      change (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      exact hk.symm ▸ a.2
    refine ⟨k, hkS, ?_⟩
    calc
      D.normalizedDegree K k =
          D.extensionNormalizedDegree K L hLK
            ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k) :=
        rfl
      _ = D.extensionNormalizedDegree K L hLK a.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) hk

end DegreeData

end

end Langlands.NYLL.ClassFormation
