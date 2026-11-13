/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 308 and Worker 192, 2026-11-13: extract M343.002–003
from commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace
with Langlands.NYLL, replace theorems by Prop-valued statement definitions,
inline M108.003 with its exact Mathlib body, and reduce imports to the
published CompleteDVF projections and Mathlib. Retain the complete source
telescope and canonical valuation subrings and maximal ideals.
The retained license and notices are in licenses/NYLL/.
-/

import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections

/-!
# Nonzero and positive ramification-index targets

These proposition definitions adapt M343.002–003 from
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationInvariants.lean`.
They retain the source hypotheses and use the exact Mathlib body of M108.003.
-/

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension

noncomputable section

universe u v w x

open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The chosen relative ramification index is nonzero. -/
def ramificationIndex_ne_zeroStatement
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] : Prop :=
  Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal ≠ 0

/-- The chosen relative ramification index is positive. -/
def ramificationIndex_posStatement
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] : Prop :=
  0 < Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal

end

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
