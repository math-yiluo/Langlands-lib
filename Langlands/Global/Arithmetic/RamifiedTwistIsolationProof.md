# Ramified twist isolation

Author: Worker 84, who wrote the proof and this explanation.

The theorem `Langlands.Global.ramifiedTwistIsolation.{u}` proves the unchanged
Library proposition `Langlands.Global.RamifiedTwistIsolationStatement.{u}` from
`Langlands.Global.Arithmetic.CharacterPrescriptionStatement`.

The proof applies three published theorems and nothing else:

- `ramifiedTwistIsolationOfInputs.{u}` (module
  `Langlands.Global.Arithmetic.RamifiedTwistIsolationReductionProof`) proves
  `FiniteOrderCharacterPrescriptionStatement.{u} →
  LocalCharactersArbitrarilyRamifiedStatement.{u} →
  RamifiedTwistIsolationStatement.{u}`;
- `finiteOrderCharacterPrescription_proof.{u}` (module
  `Langlands.Global.Arithmetic.CharacterPrescriptionProof`) discharges the
  first premise;
- `localCharactersArbitrarilyRamified.{u}` (module
  `Langlands.Global.Arithmetic.LocalCharactersArbitrarilyRamifiedProof`)
  discharges the second.

All three theorems use the same field universe `u` as the target, so the proof
is a single application term with no new definitions or hypotheses. The
statement keeps every number field, every pair of disjoint finite place sets
(empty ones included), every finite-order local prescription and every
requested depth.
