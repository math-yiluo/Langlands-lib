/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 308 and Worker 228, 2026-11-13: extract M344.002–004
from pinned commit fbd320cd8b1b06487c58227e92eb135794267709, qualify
with Langlands.NYLL, replace theorems by Prop-valued statement definitions,
reduce imports, and inline the definitionally identical M108.003/.005
wrappers using Mathlib's canonical ramification index and algebra map.
Retained license and notices are in licenses/NYLL/.
-/

import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections

noncomputable section
universe u v w x

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The image of the base maximal ideal is the ramification-index power. -/
def maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndexStatement : Prop :=
  Ideal.map (algebraMap base.valuationSubring target.valuationSubring) base.maximalIdeal =
    target.maximalIdeal ^ Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal

/-- Mapping the n-th maximal-ideal power multiplies its exponent by the index. -/
def maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndexStatement
    (n : ℕ) : Prop :=
  Ideal.map (algebraMap base.valuationSubring target.valuationSubring) (base.maximalIdeal ^ n) =
    target.maximalIdeal ^ (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal * n)

set_option linter.unusedVariables false in
/-- Base maximal-ideal-power membership maps into the corresponding target power. -/
def integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndexStatement
    {n : ℕ} {x : base.valuationSubring} (hx : x ∈ base.maximalIdeal ^ n) : Prop :=
  algebraMap base.valuationSubring target.valuationSubring x ∈
    target.maximalIdeal ^ (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal * n)

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
