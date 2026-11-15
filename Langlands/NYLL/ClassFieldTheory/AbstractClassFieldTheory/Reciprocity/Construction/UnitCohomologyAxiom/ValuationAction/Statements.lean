/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions

/-!
# Target: Galois invariance of the normalized valuation

Modified by Worker 5264, 15 November 2026: extract the statement of M032.018
from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source module imports by the published
normalized-valuation, normal-extension-action and finite-field-extension
modules. Replace the source theorem by a Prop-valued definition with the
`Statement` suffix, omitting its proof, and reword the declaration docstring
to describe the proposition. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- The proposition, from the source theorem
`valuationAt_normalExtensionAction`, that the normalized valuation of a
finite normal extension is invariant under the action of the base-field
group. -/
def valuationAt_normalExtensionActionStatement
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field.field) : Prop :=
    v.valuationAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) =
      v.valuationAt E.field a

end ValuationData

end

end Langlands.NYLL.ClassFormation
