/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 171, 14 November 2026: extract the theorem types of source
units M103.011, M103.015, M103.020, M103.021, M103.030 and M103.039 from
upstream fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and package each complete source telescope as a Prop-valued
definition with the suffix Statement. Proofs are omitted; imports are reduced
to the dependencies of the statements. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic.Definitions

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF

/-- Statement target for source unit M103.011: the valuation subring of a DVF
is a DVR. -/
def valuationSubring_isDiscreteValuationRingStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K),
    IsDiscreteValuationRing F.valuationSubring

/-- Statement target for source unit M103.015: membership in the valuation
subring is `v x <= 1`. -/
def mem_valuationSubring_iffStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K) (x : K),
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1

/-- Statement target for source unit M103.020: a DVF has a uniformizer in its
valuation subring. -/
def exists_uniformizerStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K),
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K))

set_option linter.unusedVariables false in
/-- Statement target for source unit M103.021: a uniformizer lies in the
maximal ideal. -/
def uniformizer_mem_maximalIdealStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)),
    pi ∈ F.maximalIdeal

/-- Statement target for source unit M103.030: the maximal ideal of a DVF
valuation ring is nonzero. -/
def maximalIdeal_ne_botStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K),
    F.maximalIdeal ≠ ⊥

set_option linter.unusedVariables false in
/-- Statement target for source unit M103.039: eliminate an ideal-power
quotient class through its canonical map. -/
protected def MaximalIdealPowSuccQuot.inductionOnStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K) (n : ℕ)
    {motive : F.MaximalIdealPowSuccQuot n → Prop}
    (q : F.MaximalIdealPowSuccQuot n)
    (h : ∀ a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u),
      motive (F.maximalIdealPowSuccQuotMk n a)),
    motive q

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF
