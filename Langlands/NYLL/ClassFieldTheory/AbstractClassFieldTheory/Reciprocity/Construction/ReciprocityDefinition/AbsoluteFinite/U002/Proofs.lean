/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5264, 15 November 2026:
Extract the proof of M031.002 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published AbsoluteFinite Statements module, the
proof of frobeniusFixedField_finite (M016.010) and the published proofs of
relativeTowerQuotientFinite (M026.014) and le_baseField, give the theorem the
published proposition frobeniusFixedField_absoluteFiniteStatement as its type,
and expand each extensionSubgroup A B h to its abbreviation body
B.toSubgroup.subgroupOf A.toSubgroup. The inclusion
frobeniusFixedField_le (M016.006), whose proof is not yet published, is
replaced by its source proof, inlined as the local fact hle. The published
proof of frobeniusFixedField_finite has a Statement proposition as its type,
so the local instance takes it with its unfolded type. The rest of the proof
is the source's.
Omit open KummerTheory, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition.AbsoluteFinite.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs

/-!
# The Frobenius fixed field is finite over the base field
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

section frobeniusFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Finiteness of `Σ | k`, obtained from the finite tower `Σ | K | k`. -/
theorem frobeniusFixedField_absoluteFinite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    frobeniusFixedField_absoluteFiniteStatement D K L hLK σ := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ L.toSubgroup.subgroupOf KR.field.toSubgroup) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  -- The source uses M016.006 `frobeniusFixedField_le`; `hle` is its source proof.
  have hle : (D.frobeniusFixedField KR L hLK σ).toSubgroup ≤ K.field.toSubgroup := by
    rintro g ⟨k, _, rfl⟩
    exact k.2
  let : Finite (K.field.toSubgroup ⧸
      (D.frobeniusFixedField KR L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  exact relativeTowerQuotientFinite (baseField G) K.field
    (D.frobeniusFixedField KR L hLK σ)
    hle (le_baseField K.field)

end DegreeData

end frobeniusFixedFields

end Langlands.NYLL.ClassFormation
