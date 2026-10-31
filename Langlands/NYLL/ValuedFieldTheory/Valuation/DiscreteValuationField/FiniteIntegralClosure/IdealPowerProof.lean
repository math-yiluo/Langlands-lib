/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 1045 (2026-10-30): adapt the proof of M245.012
(FiniteIntegralClosure.lean, lines 355-387) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to its published closed target,
with independent universe parameters u, v, w and the Langlands.NYLL prefix;
expand base.valuationSubring and base.maximalIdeal to the actual valuation
subring and its maximal ideal. Use the published M245.006 localness, M245.011
DVR and M245.009 nonvanishing theorems; drop the separate IsDomain step,
which instance search supplies. Replace upstream imports by published
dependencies and a focused Mathlib import. The retained license and notices
are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.DVRProof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealImageProofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealPowerStatements
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The base maximal ideal as a power of the canonical maximal ideal

The only theorem proves NYLL M245.012 as its exact published closed
proposition.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- In a finite separable extension, the ideal generated in the actual integral
closure by the base maximal ideal is a power of the canonical maximal ideal
(M245.012). -/
theorem exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow.{u, v, w} :
    ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPowStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  let A := base.valuation.valuationSubring
  let B := integralClosure A L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base
  change ∃ n : ℕ,
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ^ n
  have : IsDiscreteValuationRing B :=
    integralClosure_isDiscreteValuationRing_of_finite_separable.{u, v, w} K L base
  have hI : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≠ ⊥ :=
    integralClosure_base_maximal_map_ne_bot_of_finite_separable.{u, v, w} K L base
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨n, ?_⟩
  rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
