/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 202, 13 November 2026: extract the listed theorem types
from upstream fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and package each complete source telescope as a Prop-valued
definition. Proofs and theorem attributes are omitted; imports are reduced
to the dependencies of the statements. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport.Definitions

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

/-- Statement target for source unit M106.001. -/
def valueGroup_comap_ringEquivStatement.{u, v, w} : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L]
      {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
(v : _root_.Valuation K Γ) (e : L ≃+* K),
    MonoidWithZeroHom.valueGroup
        (.ofClass (v.comap (e : L →+* K))) =
      MonoidWithZeroHom.valueGroup (.ofClass v)

/-- Statement target for source unit M106.005. -/
def valuationSubringRingEquivOfComap_mem_maximalIdeal_iffStatement.{u, v, w} : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L]
      {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
(v : _root_.Valuation K Γ) (e : L ≃+* K)
    (x : (v.comap (e : L →+* K)).valuationSubring),
    valuationSubringRingEquivOfComap v e x ∈
        IsLocalRing.maximalIdeal v.valuationSubring ↔
      x ∈ IsLocalRing.maximalIdeal
        (v.comap (e : L →+* K)).valuationSubring

/-- Statement target for source unit M106.007. -/
def maximalIdeal_comap_valuationSubringRingEquivOfComapStatement.{u, v, w} : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L]
      {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
(v : _root_.Valuation K Γ) (e : L ≃+* K),
    (IsLocalRing.maximalIdeal v.valuationSubring).comap
        (valuationSubringRingEquivOfComap v e :
          (v.comap (e : L →+* K)).valuationSubring →+*
            v.valuationSubring) =
      IsLocalRing.maximalIdeal
        (v.comap (e : L →+* K)).valuationSubring

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
