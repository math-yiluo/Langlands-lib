/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 308, 2026-11-13: extract M345.001–002 at pinned commit
fbd320cd8b1b06487c58227e92eb135794267709, qualify with Langlands.NYLL,
replace theorem declarations by Prop-valued statement definitions,
and reduce imports. Inline the source's definitionally identical M108.003
and M108.005 wrappers with Mathlib's canonical ramification index and algebra map.
Modified by Worker 233, 2026-11-13: prepare the focused target publication
and complete the paired source correspondence and modification record.
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

/-- Additive valuation of a base integer after applying the valuation-ring map. -/
def addVal_integerMap_eq_ramificationIndex_nsmulStatement
    (a : base.valuationSubring) : Prop :=
  IsDiscreteValuationRing.addVal target.valuationSubring
      ((algebraMap base.valuationSubring target.valuationSubring) a) =
    (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal) •
      IsDiscreteValuationRing.addVal base.valuationSubring a

set_option linter.unusedVariables false in
/-- Additive valuation of an irreducible base integer after applying the map. -/
def addVal_integerMap_eq_ramificationIndex_of_irreducibleStatement
    {a : base.valuationSubring} (ha : Irreducible a) : Prop :=
  IsDiscreteValuationRing.addVal target.valuationSubring
      ((algebraMap base.valuationSubring target.valuationSubring) a) =
    ((Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal) : ℕ∞)

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
