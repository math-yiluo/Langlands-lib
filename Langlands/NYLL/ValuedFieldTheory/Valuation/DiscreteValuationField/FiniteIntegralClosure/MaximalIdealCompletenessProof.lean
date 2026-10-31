/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 384 (2026-10-31): extract the proof of M245.014
(FiniteIntegralClosure.lean, lines 428-457) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709. Prove the unchanged published
closed target with independent universes u, v, w in Langlands.NYLL.
Expand base.valuationSubring and base.maximalIdeal, adding local names
A and B. Apply the published closed localness, positive-power, mapped-ideal
completeness and positive-power reduction theorems explicitly. Preserve
the canonical localness witness and ideal equality. Replace the source
imports by the published target and proof modules.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdealCompletenessStatements
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealPowerPosProof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.CompletenessProofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPowerCompletenessProof

/-!
# Maximal-ideal completeness of finite integral closures

NYLL M245.014: completeness for the image of the base maximal ideal,
expressed as a positive power of the canonical upstairs maximal ideal,
gives completeness for that upstairs ideal.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The actual integral closure in a finite separable extension of a supplied
complete discrete valuation field is complete for its canonical maximal ideal
(M245.014), with exactly the published closed target. -/
theorem integralClosure_maximalIdeal_isAdicComplete_of_finite_separable.{u, v, w} :
    IntegralClosureMaximalIdealIsAdicCompleteOfFiniteSeparableStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  let A := base.valuation.valuationSubring
  let B := integralClosure A L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base
  change IsAdicComplete (IsLocalRing.maximalIdeal B) B
  obtain ⟨n, hnpos, hn⟩ :=
    exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow_pos.{u, v, w} K L base
  have hmap :
      IsAdicComplete ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B :=
    integralClosure_base_maximal_map_isAdicComplete_of_finite_separable.{u, v, w}
      K L base
  let : IsAdicComplete (IsLocalRing.maximalIdeal B ^ n) B := by
    have hn' :
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
          IsLocalRing.maximalIdeal B ^ n := by
      simpa only [CanonicalIntegralClosure.maximalIdeal] using hn
    simpa only [hn'] using hmap
  exact isAdicComplete_of_isAdicComplete_pow.{w, w} B B
    (IsLocalRing.maximalIdeal B) hnpos

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
