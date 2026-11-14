/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 125, 2026-11-14: extract only the type of the Prop-valued
instance M334.013 (lines 100–102) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL, suffix the name with Statement and package the complete
source telescope as a Prop-valued abbreviation, so that its proof can be
registered as an instance. The proof and the instance attribute are omitted
and the imports are reduced to the dependencies of the statement.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ResidueCharacteristic

/-!
# Primality of the residue characteristic as a typeclass fact: statement target

This module states, as a proposition, the type of the instance
`residueCharacteristic.fact_prime` of
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField

/-- Statement target for source unit M334.013, the instance
`residueCharacteristic.fact_prime`: the residue characteristic of a
local-field package is prime, packaged as `Fact` for typeclass inference. -/
abbrev residueCharacteristic.fact_primeStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K),
    Fact F.residueCharacteristic.Prime

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField
