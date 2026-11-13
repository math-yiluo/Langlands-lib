/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 133 (2026-11-13): extract only the proof of M110.004 from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean
(lines 113–134) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published ValuationSubringStatements module
of Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
and state the theorem as that module's `hasExtension_valuation_of_valuationSubring_pullbackStatement`
applied to the source binders, opening it with `unfold` before the
unchanged source tactic proof. The unused source universes x y z, the
noncomputable section and the open ResidueField namespace are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements

/-!
# `HasExtension` from exact pullback of valuation subrings (NYLL M110.004)

If the pullback of a valuation subring `B` of `L` along `K → L` is exactly the
valuation ring of `vK`, then the canonical valuation `B.valuation` extends `vK`.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- Exact pullback of valuation subrings gives a `HasExtension` proof for the
canonical valuation attached to the target valuation subring. -/
theorem hasExtension_valuation_of_valuationSubring_pullback
    (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)
    (hpullback : ∀ x : K, algebraMap K L x ∈ B.toSubring ↔
      x ∈ vK.valuationSubring) :
    hasExtension_valuation_of_valuationSubring_pullbackStatement vK B hpullback := by
  unfold hasExtension_valuation_of_valuationSubring_pullbackStatement
  apply _root_.Valuation.HasExtension.ofComapInteger
  apply le_antisymm
  · intro x hx
    have hxB : algebraMap K L x ∈ B.toSubring := by
      exact B.mem_of_valuation_le_one _ hx
    have hxA : x ∈ vK.valuationSubring := (hpullback x).1 hxB
    exact (vK.mem_integer_iff x).2
      ((vK.mem_valuationSubring_iff x).2 hxA)
  · intro x hx
    have hxA : x ∈ vK.valuationSubring := by
      exact (vK.mem_valuationSubring_iff x).1
        ((vK.mem_integer_iff x).1 hx)
    have hxB : algebraMap K L x ∈ B.toSubring := (hpullback x).2 hxA
    exact (B.valuation_le_one_iff (algebraMap K L x)).2 hxB

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
