/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# Target: the norm–valuation formula for a finite tower

Modified by Worker 5264, 15 November 2026: extract the statement of M027.007
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source module imports by the published
normalized-valuation, finite-residue-extension, relative-residue-degree and
relative-norm modules. Replace the source theorem by a Prop-valued definition
with the `Statement` suffix, omitting its proof, and reword the declaration
docstring to describe the proposition. See the paired Markdown and
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

/-- The proposition, from the source theorem `normalizedValuation_tower`
(**the norm--valuation formula**), that for a finite tower `L | K`,
`v_K ∘ N_{L|K} = f_{L|K} v_L` as values in `ZHat`. -/
def normalizedValuation_towerStatement (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (a : ambientFixedAddSubgroup A E.field.field) : Prop :=
    let ER := E.toFiniteResidueAbstractExtension D
    (ER.residueDegree : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) : v.valueGroup) : ZHat)

end ValuationData

end

end Langlands.NYLL.ClassFormation
