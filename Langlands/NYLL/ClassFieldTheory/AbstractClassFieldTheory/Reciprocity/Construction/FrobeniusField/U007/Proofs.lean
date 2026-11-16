/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 752, 16 November 2026, adapting a draft by Worker 5264
of 15 November 2026:
Extract the proof of M016.007 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusField Statements module, give the theorem
the published proposition extensionSubgroup_frobeniusFixedFieldStatement as its type, unfolded by an initial show,
and expand extensionSubgroup K.field L hLK to its abbreviation body
L.toSubgroup.subgroupOf K.field.toSubgroup. The expansion drops the
proof argument D.frobeniusFixedField_le K L hLK σ (M016.006) of the source
statement. The source rewrite with the rfl lemma M016.005
mem_frobeniusFixedField_iff becomes a change to its right-hand side. The
remaining proof is the source's.
Omit open CyclicCohomology, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements

/-!
# The subgroup of the Frobenius fixed field inside the base
-/

namespace Langlands.NYLL.ClassFormation

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Inside `G_K`, the subgroup attached to the actual field `Σ` is
literally the quotient-projection inverse image used in its definition. -/
theorem extensionSubgroup_frobeniusFixedField (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    extensionSubgroup_frobeniusFixedFieldStatement D K L hLK σ := by
  show (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup =
      D.frobeniusFixedSubgroupWithin K L hLK σ
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

end DegreeData

end Langlands.NYLL.ClassFormation
