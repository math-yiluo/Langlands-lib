/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 308 and Worker 431, 2026-11-13/14: adapt the selected source
result at commit fbd320cd8b1b06487c58227e92eb135794267709 to its published
Langlands.NYLL Statement target, using the published CompleteDVF projections and
the exact Mathlib bodies of M108.003/.005. The proof is rerouted through Mathlib's
unconditional `Ideal.le_pow_ramificationIdx'` instead of the source's ideal-image
equality. See the paired Markdown for the proof route, source correspondence and
modifications. Retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.ImageStatements

noncomputable section
universe u v w x
namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- Elements of the `n`-th power of the base maximal ideal map into the
`(e * n)`-th power of the target maximal ideal, where `e` is the canonical
ramification index `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal`. -/
theorem integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndex
    {n : ℕ} {x : base.valuationSubring} (hx : x ∈ base.maximalIdeal ^ n) :
    integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndexStatement base target hx := by
  change algebraMap base.valuationSubring target.valuationSubring x ∈
    target.maximalIdeal ^ (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal * n)
  have hle : Ideal.map (algebraMap base.valuationSubring target.valuationSubring)
      (base.maximalIdeal ^ n) ≤
      target.maximalIdeal ^ (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal * n) := by
    rw [Ideal.map_pow, pow_mul]
    exact Ideal.pow_right_mono Ideal.le_pow_ramificationIdx' n
  exact hle (Ideal.mem_map_of_mem _ hx)

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
