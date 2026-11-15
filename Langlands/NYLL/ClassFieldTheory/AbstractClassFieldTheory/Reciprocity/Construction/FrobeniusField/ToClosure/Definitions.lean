/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions

/-!
# The restriction from a Frobenius fixed field to the Frobenius closure

Modified by Worker 5264, 15 November 2026: extract M016.021
`frobeniusFixedFieldToClosure` from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefixing the namespace with
`Langlands.NYLL`. In the body, the source applications of the theorems
M016.006 `frobeniusFixedField_le` and M016.007
`extensionSubgroup_frobeniusFixedField` are replaced by local hypotheses
proved by the source proofs of these theorems; in the latter proof the
rewrite with the `rfl` lemma M016.005 `mem_frobeniusFixedField_iff` becomes
a `change` to its right-hand side. As in the published sibling modules,
`extensionSubgroup K.field L hLK` is expanded to its exact Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup`. The source import is replaced
by the published FrobeniusField definitions module. The source variable
declaration, docstring, binders and the remaining body are retained. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Restriction from the actual group `G_Σ` to the group-dual `Γ`. -/
def frobeniusFixedFieldToClosure (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup →*
      D.frobeniusClosure K L hLK σ where
  toFun s := by
    have hle :
        (D.frobeniusFixedField K L hLK σ).toSubgroup ≤ K.field.toSubgroup := by
      rintro g ⟨k, _, rfl⟩
      exact k.2
    let k : K.field.toSubgroup :=
      Subgroup.inclusion hle s
    refine ⟨QuotientGroup.mk k, ?_⟩
    have hsub :
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
            K.field.toSubgroup =
          D.frobeniusFixedSubgroupWithin K L hLK σ := by
      ext k
      change
        (k.1 ∈ D.frobeniusFixedField K L hLK σ) ↔
          k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ
      change
        (∃ t : K.field.toSubgroup,
            t ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ t.1 = k.1) ↔
          k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ
      constructor
      · rintro ⟨t, ht, htk⟩
        have : t = k := by
          apply Subtype.ext
          exact htk
        simpa [this] using ht
      · intro hk
        exact ⟨k, hk, rfl⟩
    have hk : k ∈
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup := s.2
    rw [hsub] at hk
    exact hk
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' := by
    intro a b
    apply Subtype.ext
    rfl

end DegreeData

end

end Langlands.NYLL.ClassFormation
