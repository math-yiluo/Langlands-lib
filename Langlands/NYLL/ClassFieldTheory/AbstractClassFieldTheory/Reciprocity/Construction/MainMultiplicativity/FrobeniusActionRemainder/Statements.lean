/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.NormalizedDegreeContinuous.Definitions

/-!
# Target: Frobenius action remainders have degree zero

Modified by Worker 5264, 15 November 2026: state the source theorem M053.004
`DegreeData.frobeniusActionRemainder_mem_degreeKernel` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by focused published imports, omit
the proof, the rest of the source file and the unused `open KummerTheory`
and `open CategoryTheory`, and turn off the unused-variable linter for the
hypothesis `hφ`, which the proposition does not mention. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

set_option linter.unusedVariables false in
/-- Target: if `φ` has Frobenius exponent one, its action remainder has
normalized degree zero. -/
def frobeniusActionRemainder_mem_degreeKernelStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) : Prop :=
    D.frobeniusActionRemainder K L hLK φ σ ∈
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker

end DegreeData

end

end Langlands.NYLL.ClassFormation
