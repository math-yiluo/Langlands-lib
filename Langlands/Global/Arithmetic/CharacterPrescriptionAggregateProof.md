# The coherent finite-character prescription inputs

Author: Worker 84, who wrote the proof and this explanation.

The theorem `Langlands.Global.characterPrescription.{u}` proves the unchanged
Library proposition `Langlands.Global.CharacterPrescriptionStatement.{u}` from
`Langlands.Global.Arithmetic.CharacterPrescriptionStatement`. That proposition
is the conjunction of three statements. The proof supplies each conjunct from
published theorems:

1. `FiniteOrderCharacterPrescriptionStatement.{u}` is
   `finiteOrderCharacterPrescription_proof.{u}` (module
   `Langlands.Global.Arithmetic.CharacterPrescriptionProof`).
2. `LocalCharactersArbitrarilyRamifiedStatement.{u}` is
   `localCharactersArbitrarilyRamified.{u}` (module
   `Langlands.Global.Arithmetic.LocalCharactersArbitrarilyRamifiedProof`).
3. `RamifiedTwistIsolationStatement.{u}` is obtained by applying
   `ramifiedTwistIsolationOfInputs.{u}` (module
   `Langlands.Global.Arithmetic.RamifiedTwistIsolationReductionProof`) to the
   two theorems above.

The anonymous-constructor term builds the conjunction directly. It adds no
definitions or hypotheses and uses only the field universe `u` of the target.
The CM infinity-type and general-position inputs are separate statements and
are not part of this proposition.
