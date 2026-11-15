/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions

/-!
# Targets: valuations along a finite totally ramified extension

Modified by Worker 5264, 15 November 2026: state the source theorems M075.029
`abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified` and
M075.030 `abstractReciprocity_totallyRamified_valuation_forces_exponent_zero`
of `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, replace the source imports by focused published imports, omit
the proofs, the rest of the source file and the unused
`open CyclicCohomology` and `open CategoryTheory`, and turn off the
unused-variable linter for the hypotheses `hTot`, `hk` and `hx`, which the
propositions do not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

set_option linter.unusedVariables false in
/-- Target: in a finite totally ramified extension, the normalized valuation
of an element from the lower field is multiplied by the extension degree
after inclusion into the upper field.  This is the valuation identity used
for `M/M⁰`. -/
def abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamifiedStatement
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (x : ambientFixedAddSubgroup A E.base.field) : Prop :=
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
      v.valueGroup) : ZHat) =
      (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ZHat)

set_option linter.unusedVariables false in
/-- Target: the exact `k = 0` valuation endpoint of the totally ramified
argument.  Here `K = M⁰`, `L = M`, and `x` is the element constructed in
the fixed subgroup. -/
def abstractReciprocity_totallyRamified_valuation_forces_exponent_zeroStatement
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ) (hk : k < (E.degree : ℕ))
    (x : ambientFixedAddSubgroup A E.base.field)
    (hx :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ZHat) =
        Int.castRingHom ZHat (k : ℤ)) : Prop :=
    k = 0

end

end Langlands.NYLL.ClassFormation
