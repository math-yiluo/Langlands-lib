/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion

/-!
# Target: the additive order of a prime class in an unramified norm quotient

Modified by Worker 5264, 15 November 2026: state the source theorem M058.014
`ValuationData.primeClass_addOrderOf` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by focused published imports, omit
the proof and the rest of the source file, and turn off the unused-variable
linter for the hypotheses `hUnramified` and `hπ`, which the proposition does
not mention. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

set_option linter.unusedVariables false in
/-- Target: a prime class has exact additive order `[L : K]` in an
unramified norm quotient.  The lower bound is read after reduction in
`ℤ̂/nℤ̂`; the upper bound is the norm of the included prime. -/
def primeClass_addOrderOfStatement
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    Prop :=
    addOrderOf
      (finiteNormClass A K.field L hLK π) =
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)

end ValuationData

end

end Langlands.NYLL.ClassFormation
