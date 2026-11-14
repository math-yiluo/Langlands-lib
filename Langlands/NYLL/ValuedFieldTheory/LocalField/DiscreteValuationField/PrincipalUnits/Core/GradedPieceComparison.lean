/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299 and Worker 479, 2026-11-13/14: extract NYLL unit
M231.033 at commit fbd320cd8b1b06487c58227e92eb135794267709, prefix
namespaces with Langlands.NYLL, and import the published focused modules.
See the paired Markdown for all modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.SuccessorQuotient
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.Filtration
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.GradedPiece

/-!
# Concrete and abstract principal-unit graded pieces

Adapted from NYLL M231.033,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean`,
lines 538–547, at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

variable {K : Type u} [Field K]
variable (F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The concrete complete-DVF adjacent quotient agrees with the generic
graded-piece wrapper through explicit public equivalences. -/
def principalUnitSuccQuotEquivGradedPiece (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPiece n :=
  (higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n).trans
    ((AntitoneSubgroupFiltration.principalUnitGradedPieceEquivSubquotient
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) n).trans
      (AntitoneSubgroupFiltration.principalUnitSubquotientConcreteEquiv
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) n (n + 1))).symm

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

end
