/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 764 (2026-10-30): adapt the proof of M245.011
(FiniteIntegralClosure.lean, lines 329-353) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to its published closed target,
with independent universe parameters u, v, w and the Langlands.NYLL prefix;
expand base.valuationSubring to the actual valuation subring. Use the
published M245.006 localness and M245.010 nonfield theorems. Obtain the
fraction-ring and domain facts by Mathlib instance search instead of the
base_valuationSubring_isFractionRing wrapper and local instances, take the
Noetherian property from the Dedekind property instead of a separate
integralClosure.isNoetherianRing step, and pass the Dedekind proof directly
to the current Mathlib IsDiscreteValuationRing.TFAE. Replace upstream imports
by published dependencies and focused Mathlib imports. The retained license
and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.DVRStatements
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.LocalnessProof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.NotFieldProof
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# The finite integral closure over a complete DVF is a DVR

The only theorem proves NYLL M245.011 as its exact published closed
proposition.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The actual integral closure of the valuation subring of a complete DVF in a
finite separable extension is a discrete valuation ring (M245.011). -/
theorem integralClosure_isDiscreteValuationRing_of_finite_separable.{u, v, w} :
    IntegralClosureIsDiscreteValuationRingOfFiniteSeparableStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  let A := base.valuation.valuationSubring
  let B := integralClosure A L
  have : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base
  have hD : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have hB : ¬ IsField B :=
    integralClosure_not_isField_of_finite_separable.{u, v, w} K L base
  exact ((IsDiscreteValuationRing.TFAE B hB).out 3 1).mp hD

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
