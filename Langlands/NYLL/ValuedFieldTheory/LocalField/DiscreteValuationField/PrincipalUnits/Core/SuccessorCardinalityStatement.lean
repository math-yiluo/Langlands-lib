/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: extract the indicated units at commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, and isolate the successor-quotient cardinality target. Import focused
published data. See the paired Markdown for all modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.SuccessorQuotient

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

set_option linter.unusedVariables false in
/-- Cardinality form of the residue-field identification at positive levels (M231.063). -/
def card_principalUnitSuccQuot_eq_residue_of_uniformizerStatement
    {K : Type u} [Field K]
    (F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    [Finite F.residueField]
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) : Prop :=
  Nat.card (principalUnitSuccQuot F n) = Nat.card F.residueField

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
