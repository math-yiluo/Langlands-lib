/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 461, 2026-11-14: adapt only the proof of M334.011
(lines 87–93) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to its published closed target
residueCharacteristic_primeStatement.{u, v}; qualify the namespace with
Langlands.NYLL, introduce the target's binders with `intro K _ F` before
the unchanged source tactic body, replace the source imports by the
published statement module and Mathlib.Algebra.CharP.Lemmas, remove the
unused universes w and x, and replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristicPrimeStatement
import Mathlib.Algebra.CharP.Lemmas

/-!
# Primality of the residue characteristic: proof

This module proves the published target `residueCharacteristic_primeStatement`
for the theorem `residueCharacteristic_prime` of
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
-/

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField

/-- Proves the primality statement `Nat.Prime F.residueCharacteristic`
for every local-field package `F`. -/
theorem residueCharacteristic_prime : residueCharacteristic_primeStatement.{u, v} := by
  intro K _ F
  change Nat.Prime (ringChar F.toCompleteDVF.residueField)
  let : NoZeroDivisors F.toCompleteDVF.residueField :=
    GroupWithZero.noZeroDivisors
  exact CharP.prime_ringChar F.toCompleteDVF.residueField

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField
