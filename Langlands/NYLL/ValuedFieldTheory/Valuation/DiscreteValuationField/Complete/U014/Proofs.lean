/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements

/-!
# NYLL M107.014: adic completeness of the valuation subring of a complete DVF

Modified by Worker 5264, 15 November 2026: prove the published target
`CompleteDVF.isAdicCompleteStatement` (M107.014) by the source proof of
`CompleteDVF.isAdicComplete` in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source term
`Valuation.isAdicComplete F.valuation` (M107.002, not yet published) by its
own source body `Valuation.IsCompleteDiscrete.isAdicComplete (val := F.valuation)`,
replace the source imports by the published statement module and omit the universe
`w` and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v

namespace DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The complete DVR model is complete for its maximal-ideal-adic topology. -/
theorem isAdicComplete (F : CompleteDVF.{u, v} K) :
    isAdicCompleteStatement F := by
  show IsAdicComplete F.maximalIdeal F.valuationSubring
  change IsAdicComplete
    (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
    F.valuation.valuationSubring
  exact Valuation.IsCompleteDiscrete.isAdicComplete (val := F.valuation)

end CompleteDVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
