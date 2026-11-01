/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 785 (2026-10-31): adapt only the existence,
HasExtension and IsIntegralClosure part of the proof of M245.018,
exists_integralClosure_standard_fundamental_identity
(FiniteIntegralClosure.lean, lines 645-674, ambient lines 23 and 30-31)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709, and omit
the fundamental-identity part (lines 675-685). Prove the unchanged
published closed target in Langlands.NYLL at independent universes u, v, w,
obtaining the witness from the published M245.017 theorem
exists_integralClosure_standard_completeDVF. Replace the contraction helper
algebraMap_mem_integralClosure_valuationSubring_iff
(ChevalleyExtension.lean, lines 190-213) by a local proof from Mathlib's
isIntegral_algebraMap_iff and IsIntegrallyClosed.isIntegral_iff. Expand the
CompleteDVF valuationSubring abbreviations and qualify Mathlib's
HasExtension. Replace the upstream imports by the published target and
M245.017 proof and a focused Mathlib import. The retained license and
notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFExtensionStatement
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFProof
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Complete-DVF extension with its actual integral closure: proof

The complete-DVF witness of NYLL M245.017 extends the supplied base
valuation, and once that extension is installed its valuation subring is
the actual integral closure of the base valuation subring in the field.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- Every supplied finite separable algebra over a complete DVF admits one
complete-DVF extension whose valuation subring is the actual integral
closure (the existence consequence of M245.018), with precisely the
published closed target. -/
theorem exists_integralClosure_standard_completeDVF_extension.{u, v, w} :
    ExistsIntegralClosureStandardCompleteDVFExtensionStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  obtain ⟨target, hmem, _hequiv⟩ :=
    exists_integralClosure_standard_completeDVF.{u, v, w} K L base
  have hcontract (a : K) :
      algebraMap K L a ∈
          (integralClosure base.valuation.valuationSubring L).toSubring ↔
        a ∈ base.valuation.valuationSubring := by
    change IsIntegral base.valuation.valuationSubring (algebraMap K L a) ↔ _
    rw [isIntegral_algebraMap_iff, IsIntegrallyClosed.isIntegral_iff]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  have hExt : _root_.Valuation.HasExtension base.valuation target.valuation := by
    apply _root_.Valuation.HasExtension.ofComapInteger
    ext a
    change
      algebraMap K L a ∈ target.valuation.valuationSubring ↔
        a ∈ base.valuation.valuationSubring
    rw [hmem]
    exact hcontract a
  refine ⟨target, hExt, ?_⟩
  let : _root_.Valuation.HasExtension base.valuation target.valuation := hExt
  refine
    { algebraMap_injective := ?_
      isIntegral_iff := ?_ }
  · intro x y hxy
    exact Subtype.ext hxy
  · intro z
    constructor
    · intro hz
      have hzmem :
          z ∈ (integralClosure base.valuation.valuationSubring L).toSubring := hz
      exact ⟨⟨z, (hmem z).2 hzmem⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact (hmem (y : L)).1 y.2

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
