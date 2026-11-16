/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements

/-!
# NYLL M107.023: a uniformizer of a complete DVF lies in the maximal ideal

Modified by Worker 5264, 15 November 2026: prove the published target
`CompleteDVF.uniformizer_mem_maximalIdealStatement` (M107.023) following the
source proof of `CompleteDVF.uniformizer_mem_maximalIdeal` in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source term
`F.toDVF.uniformizer_mem_maximalIdeal hpi` (the unpublished M103.021) by its
own source body, a `change` to the maximal ideal of the valuation subring of
`F.valuation` followed by the Mathlib theorems `Valuation.mem_maximalIdeal_iff`
and `Valuation.IsUniformizer.val_lt_one`,
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

/-- Every chosen uniformizer lies in the maximal ideal. -/
theorem uniformizer_mem_maximalIdeal (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    uniformizer_mem_maximalIdealStatement F hpi := by
  show pi ∈ F.maximalIdeal
  change pi ∈ IsLocalRing.maximalIdeal F.valuation.valuationSubring
  exact (_root_.Valuation.mem_maximalIdeal_iff (v := F.valuation)).2 hpi.val_lt_one

end CompleteDVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
