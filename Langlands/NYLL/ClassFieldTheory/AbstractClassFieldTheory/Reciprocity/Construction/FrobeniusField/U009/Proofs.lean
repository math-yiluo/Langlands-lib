/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 752, 16 November 2026, adapting a draft by Worker 5264
of 15 November 2026:
Extract the proof of M016.009 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusField Statements module, give the theorem
the published proposition fieldInertia_le_frobeniusFixedFieldStatement as its type, unfolded by an initial show,
and expand extensionSubgroup K.field L hLK to its abbreviation body
L.toSubgroup.subgroupOf K.field.toSubgroup. The source application of the theorem M016.008
extensionInertiaWithin_le_frobeniusFixedSubgroupWithin is replaced by a local
hypothesis hle proved by the source proof of M016.008. The remaining proof
is the source's.
Omit open CyclicCohomology, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements

/-!
# The ambient inertia subgroup lies in the Frobenius fixed field
-/

namespace Langlands.NYLL.ClassFormation

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Ambient form of `I_L ≤ G_Σ`. -/
theorem fieldInertia_le_frobeniusFixedField (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    fieldInertia_le_frobeniusFixedFieldStatement D K L hLK σ := by
  show (D.fieldInertia L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup
  have hle : D.extensionInertiaWithin K.field L hLK ≤
      D.frobeniusFixedSubgroupWithin K L hLK σ := by
    intro k hk
    change QuotientGroup.mk k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup
    rw [(QuotientGroup.eq_one_iff k).2 hk]
    exact Subgroup.one_mem _
  intro g hg
  let k : K.field.toSubgroup := ⟨g, hLK hg.1⟩
  have hkE : k ∈ L.toSubgroup.subgroupOf K.field.toSubgroup := hg.1
  have hkI : k ∈ D.fieldInertiaWithin K.field := hg.2
  exact ⟨k,
    hle ⟨hkE, hkI⟩,
    rfl⟩

end DegreeData

end Langlands.NYLL.ClassFormation
