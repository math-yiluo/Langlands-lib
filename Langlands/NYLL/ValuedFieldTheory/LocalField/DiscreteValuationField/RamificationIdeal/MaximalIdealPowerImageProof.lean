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
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.ImageStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.MaximalIdealImageProof

noncomputable section
universe u v w x
namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
variable [base.valuation.HasExtension target.valuation]

theorem maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex
    (n : ℕ) :
    maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndexStatement base target n := by
  change Ideal.map (algebraMap base.valuationSubring target.valuationSubring)
    (base.maximalIdeal ^ n) =
    target.maximalIdeal ^ (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal * n)
  rw [Ideal.map_pow, maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex base target,
    pow_mul]

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
