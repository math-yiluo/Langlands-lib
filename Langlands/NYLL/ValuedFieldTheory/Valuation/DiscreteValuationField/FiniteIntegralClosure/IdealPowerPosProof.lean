/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 384 (2026-10-30): extract the proof of M245.013
(FiniteIntegralClosure.lean, lines 389-426) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, proving its published closed
target with independent universes u, v, w in Langlands.NYLL. Expand the
source abbreviations base.valuationSubring and base.maximalIdeal; apply
the published closed M245.006, M245.008 and M245.012 theorems explicitly.
Replace upstream imports by published proof and target modules. Preserve
the localness witness and the source argument excluding the zero exponent.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealPowerStatements
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealPowerProof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealImageProofs

/-!
# The base maximal ideal as a positive maximal-ideal power

This module proves only NYLL M245.013 as its published closed proposition.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- In a finite separable extension, the ideal generated in the actual integral
closure by the base maximal ideal is a positive power of the canonical maximal
ideal (M245.013). -/
theorem exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow_pos.{u, v, w} :
    ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPowPosStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  let A := base.valuation.valuationSubring
  let B := integralClosure A L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base
  change ∃ n : ℕ,
    0 < n ∧
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ^ n
  obtain ⟨n, hn⟩ :=
    exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow.{u, v, w} K L base
  refine ⟨n, ?_, hn⟩
  by_contra hnot
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
  have htop : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = ⊤ := by
    simpa [hn0] using hn
  have hle :
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ IsLocalRing.maximalIdeal B :=
    integralClosure_base_maximal_map_le_maximalIdeal_of_finite_separable.{u, v, w} K L base
  have htop_le : (⊤ : Ideal B) ≤ IsLocalRing.maximalIdeal B := by
    simpa [htop] using hle
  exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp htop_le)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
