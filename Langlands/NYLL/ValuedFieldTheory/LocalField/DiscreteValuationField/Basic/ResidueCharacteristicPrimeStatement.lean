/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 125, 2026-11-13: extract only the type of M334.011
(lines 87–89) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL, suffix the name with Statement and package the complete
source telescope as a Prop-valued definition. The proof is omitted and
the imports are reduced to the dependencies of the statement.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristic

/-!
# Primality of the residue characteristic: statement target

This module states, as a proposition, the theorem
`residueCharacteristic_prime` of
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField

/-- Statement target for source unit M334.011: the residue characteristic of
a local-field package is a prime number. -/
def residueCharacteristic_primeStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K),
    Nat.Prime F.residueCharacteristic

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField
