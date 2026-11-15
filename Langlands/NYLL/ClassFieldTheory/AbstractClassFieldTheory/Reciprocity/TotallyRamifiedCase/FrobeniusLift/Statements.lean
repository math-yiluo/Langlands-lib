/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# Target: degree-one Frobenius lifts in totally ramified extensions

Modified by Worker 5264, 15 November 2026: state the source theorem M079.001
`DegreeData.exists_degreeOneFrobeniusLiftOfTotallyRamified` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append
`Statement` to the name, omit the proof and the unused
`open KummerTheory` and `open CyclicCohomology`, and turn off the
unused-variable linter for the hypothesis `hTot`, which the proposition does
not mention. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

set_option linter.unusedVariables false in
/-- Target: every automorphism of a totally ramified Galois extension has a
Frobenius lift of exponent one. -/
def exists_degreeOneFrobeniusLiftOfTotallyRamifiedStatement
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) : Prop :=
    ∃ σ : D.FrobeniusElements K L.field L.below,
      D.frobeniusExponent K L.field L.below σ = 1 ∧
      L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below σ) = q

end DegreeData

end Langlands.NYLL.ClassFormation
