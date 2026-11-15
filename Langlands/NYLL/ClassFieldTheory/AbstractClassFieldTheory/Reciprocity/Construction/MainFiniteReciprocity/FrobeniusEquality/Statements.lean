/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Target: equal restriction and exponent give equal Frobenius lifts

Modified by Worker 5264, 15 November 2026: state the source theorem M065.010
`DegreeData.frobenius_eq_of_restriction_eq_of_exponent_eq` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainFiniteReciprocity.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source import by focused published imports, omit
the proof, the rest of the source file and the unused `open KummerTheory`,
`open CategoryTheory` and `open scoped BigOperators`, and turn off the
unused-variable linter for the hypotheses `hRestriction` and `hExponent`,
which the proposition does not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

set_option linter.unusedVariables false in
/-- Target: equal restrictions and equal positive degrees give equal
Frobenius lifts.  This is the first case in the lift-independence proof. -/
def frobenius_eq_of_restriction_eq_of_exponent_eqStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction : D.frobeniusRestriction K L hLK σ =
      D.frobeniusRestriction K L hLK τ)
    (hExponent : D.frobeniusExponent K L hLK σ =
      D.frobeniusExponent K L hLK τ) : Prop :=
    σ = τ

end DegreeData

end

end Langlands.NYLL.ClassFormation
