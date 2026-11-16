/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 752, 16 November 2026, adapting a draft by Worker 5264
of 15 November 2026:
Extract the proof of M016.005 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusField Statements module, give the theorem
the published proposition mem_frobeniusFixedField_iffStatement as its type, unfolded by an initial show,
and expand extensionSubgroup K.field L hLK to its abbreviation body
L.toSubgroup.subgroupOf K.field.toSubgroup. The proof is the source's rfl, as Iff.rfl after the show.
Omit the source @[simp] attribute, since the theorem's type is a Statement
constant. Omit open CyclicCohomology, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements

/-!
# Membership in the Frobenius fixed field
-/

namespace Langlands.NYLL.ClassFormation

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- An element lies in the Frobenius fixed field exactly when Frobenius fixes its restriction. -/
theorem mem_frobeniusFixedField_iff (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) (g : G) :
    mem_frobeniusFixedField_iffStatement D K L hLK σ g := by
  show g ∈ D.frobeniusFixedField K L hLK σ ↔
      ∃ k : K.field.toSubgroup,
        k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ k.1 = g
  exact Iff.rfl

end DegreeData

end Langlands.NYLL.ClassFormation
