/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.FixedCarrier.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions

/-!
# Target: normalized valuation is invariant under the quotient action

Modified by Worker 5264, 15 November 2026: state the source theorem M083.003
`ValuationData.valuationAt_extensionFixedRepresentation_action` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source import by focused published imports, and
omit the proof, the rest of the source file and the unused
`open KummerTheory` and `open CategoryTheory`. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- Target: normalized valuation is invariant under the actual quotient
action.  This is the quotient-representation form of the unit-cohomology
axiom's `valuationAt_normalExtensionAction`. -/
def valuationAt_extensionFixedRepresentation_actionStatement
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (q : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (a : (extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal).V) : Prop :=
    v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ q a)) =
      v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal a)

end ValuationData

end

end Langlands.NYLL.ClassFormation
