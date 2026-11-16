/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 289, 2026-11-16: isolate the proof of M334.013
(lines 100–103) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL, state the theorem at the published closed target
residueCharacteristic.fact_primeStatement.{u, v}, introduce its binders,
and retain the source body and default-priority instance registration via
`attribute [instance]`. Replace the source imports by the published target
and residueCharacteristic_prime proof modules, omit unused universes w x,
and replace the module documentation. Worker 125 supplied this proof route.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristicFactPrimeStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristicPrimeProof

/-!
# Primality of the residue characteristic as a typeclass fact: proof

This module proves the published target `residueCharacteristic.fact_primeStatement`
and registers the source instance M334.013.
-/

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField

/-- Registers the mathematical fact `Fact F.residueCharacteristic.Prime` for typeclass inference. -/
theorem residueCharacteristic.fact_prime : residueCharacteristic.fact_primeStatement.{u, v} := by
  intro K _ F
  exact ⟨F.residueCharacteristic_prime⟩

attribute [instance] residueCharacteristic.fact_prime

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField
