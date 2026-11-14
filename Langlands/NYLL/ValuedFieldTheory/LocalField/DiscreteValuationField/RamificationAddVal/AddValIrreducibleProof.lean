/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 308, 2026-11-13: adapt the selected source result at
commit fbd320cd8b1b06487c58227e92eb135794267709 to its published Langlands.NYLL
Statement target. Reuse the published CompleteDVF projections and exact
Mathlib bodies of M108.003/.005. See the paired Markdown for the proof route,
source correspondence and modifications. Retained license and notices are
in licenses/NYLL/.
-/
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal.RestrictionStatements
import Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints

noncomputable section
universe u v w x
namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
variable [base.valuation.HasExtension target.valuation]

theorem addVal_integerMap_eq_ramificationIndex_of_irreducible
    {a : base.valuationSubring} (ha : Irreducible a) :
    addVal_integerMap_eq_ramificationIndex_of_irreducibleStatement base target ha := by
  exact P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.HerbrandPortG3.addVal_algebraMap_irreducible_eq_ramificationIdx
    (R := base.valuationSubring) (S := target.valuationSubring)
    (Valuation.HasExtension.algebraMap_injective
      (vK := base.valuation) (vA := target.valuation)) ha

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
