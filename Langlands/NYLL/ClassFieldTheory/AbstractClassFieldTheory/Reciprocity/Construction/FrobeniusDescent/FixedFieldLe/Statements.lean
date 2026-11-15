/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions

/-!
# Target: a Frobenius lift with trivial restriction has fixed field containing `L`

Modified by Worker 5264, 15 November 2026: state the source theorem M017.004
`frobeniusFixedField_le_of_restriction_eq_one` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, expand `extensionSubgroup K.field L hLK` to its exact Mathlib
body `L.toSubgroup.subgroupOf K.field.toSubgroup`, keep the source variable
declaration, parameters and binder kinds, omit the proof and the unused
`open CyclicCohomology`, and turn off the unused-variable linter for the
hypotheses that the conclusion does not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

set_option linter.unusedVariables false in
/-- Target: if a Frobenius lift restricts trivially to `L`, its fixed field
contains `L`, that is, the closed subgroup of the fixed field lies in `G_L`. -/
def frobeniusFixedField_le_of_restriction_eq_oneStatement
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusRestriction K L hLK σ = 1) : Prop :=
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤
      L.toSubgroup

end DegreeData

end

end Langlands.NYLL.ClassFormation
