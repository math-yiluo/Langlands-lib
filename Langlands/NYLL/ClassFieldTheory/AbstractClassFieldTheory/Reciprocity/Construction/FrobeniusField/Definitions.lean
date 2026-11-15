/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions

/-!
# The abstract reciprocity construction: the field fixed by a Frobenius lift

Modified by Worker 5264: extract M016.001 `frobeniusFixedSubgroupWithin` and
M016.004 `frobeniusFixedField` from the pinned NYLL FrobeniusField source with
the Langlands.NYLL namespace prefix. In the closedness proof inside M016.004,
the source application of the theorem M016.003
`frobeniusFixedSubgroupWithin_isClosed` is replaced by a local hypothesis
proved by the source proof of M016.003. As in the published sibling modules,
`extensionSubgroup K.field L hLK` is expanded to its exact Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup`. The source import is replaced by
the published FrobeniusClosure definitions module. The source variable
declaration, docstrings, binders and remaining construction bodies are
retained. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The subgroup `G_Σ ≤ G_K`: the inverse image of
`Γ = closure ⟨σ⟩` under `G_K → G_K / I_L`. -/
def frobeniusFixedSubgroupWithin (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Subgroup K.field.toSubgroup :=
  (D.frobeniusClosure K L hLK σ).toSubgroup.comap
    (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))

/-- The actual abstract field `Σ` fixed by the chosen Frobenius lift.
Its absolute Galois subgroup is the inverse image of `Γ`, now regarded as
a closed subgroup of the ambient group `G`. -/
def frobeniusFixedField (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : ClosedSubgroup G where
  toSubgroup :=
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
      K.field.toSubgroup.subtype
  isClosed' := by
    have hclosed : IsClosed
        (D.frobeniusFixedSubgroupWithin K L hLK σ : Set K.field.toSubgroup) := by
      change IsClosed
        ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ⁻¹'
          ((D.frobeniusClosure K L hLK σ).toSubgroup : Set
            (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)))
      exact (D.frobeniusClosure K L hLK σ).isClosed'.preimage
        continuous_quotient_mk'
    change IsClosed
      (Subtype.val ''
        (D.frobeniusFixedSubgroupWithin K L hLK σ : Set K.field.toSubgroup))
    exact K.field.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      hclosed

end DegreeData

end
end Langlands.NYLL.ClassFormation
