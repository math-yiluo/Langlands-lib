/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions

/-!
# Target: the Frobenius fixed field is finite over the base field

Modified by Worker 5264, 15 November 2026: state the source theorem M031.002
`frobeniusFixedField_absoluteFinite` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, expand each `extensionSubgroup A B h` to its exact Mathlib body
`B.toSubgroup.subgroupOf A.toSubgroup` (which drops the proof argument
`le_baseField ...`), keep the source universe, variable declaration,
parameters, binder kinds and the named-argument proofs of `hLnormal`, omit
the proof and the unused `open KummerTheory` and `open CyclicCohomology`, and
turn off the unused-variable linter for the instance hypothesis `hLfinite`,
which the conclusion does not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

noncomputable section

section frobeniusFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

set_option linter.unusedVariables false in
/-- Target: finiteness of `Σ | k` for the fixed field `Σ` of a Frobenius
element over a finite abstract field `K`. -/
def frobeniusFixedField_absoluteFiniteStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    Prop :=
    Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
          (hLnormal := by
            simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)
          σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)

end DegreeData

end frobeniusFixedFields

end

end Langlands.NYLL.ClassFormation
