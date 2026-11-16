/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5264, 15 November 2026:
Extract the proof of M016.010 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusField Statements module and the
proof of frobeniusFixedField_finiteIndex (M014.039), give the theorem the
published proposition frobeniusFixedField_finiteStatement as its type, unfolded
by an initial show, and expand extensionSubgroup K.field L hLK and
extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ) _ to their
abbreviation bodies L.toSubgroup.subgroupOf K.field.toSubgroup and
(D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup; the
expanded statement needs no inclusion proof, so the source's use of
frobeniusFixedField_le (M016.006) disappears. The source rewrite with
extensionSubgroup_frobeniusFixedField (M016.007), whose proof is not yet
published, uses that theorem's source proof, inlined as the local equation
hSeq (with the definitional unfolding of mem_frobeniusFixedField_iff, M016.005,
by change). The rest of the proof is the source's.
Omit open CyclicCohomology, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.U039.Proofs

/-!
# The Frobenius fixed field is finite
-/

namespace Langlands.NYLL.ClassFormation

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- finiteness of the Frobenius fixed field on the actual field side: `Σ | K` is finite. -/
theorem frobeniusFixedField_finite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusFixedField_finiteStatement D K L hLK σ := by
  show Finite
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup)
  let N := D.extensionInertiaWithin K.field L hLK
  let Q := K.field.toSubgroup ⧸ N
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  have hfin : Finite
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
    D.frobeniusFixedField_finiteIndex K L hLK σ
  let : Finite (Q ⧸ Γ) := by
    simpa [Q, Γ, N] using hfin
  have hΓ : Γ.index ≠ 0 := Γ.index_ne_zero_of_finite
  have hS : S.index ≠ 0 := by
    rw [show S = Γ.comap (QuotientGroup.mk' N) by rfl]
    rw [Subgroup.index_comap_of_surjective Γ
      (QuotientGroup.mk'_surjective N)]
    exact hΓ
  -- The source rewrites with M016.007 `extensionSubgroup_frobeniusFixedField`;
  -- `hSeq` is its source proof.
  have hSeq :
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup =
        D.frobeniusFixedSubgroupWithin K L hLK σ := by
    ext k
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
  apply Nat.finite_of_card_ne_zero
  change
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
      K.field.toSubgroup).index ≠ 0
  rw [hSeq]
  exact hS

end DegreeData

end Langlands.NYLL.ClassFormation
