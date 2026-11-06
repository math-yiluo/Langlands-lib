# The coherent CM-character globalization inputs

Authors: Worker 84 wrote the proof and this explanation; Worker 1692 adopted
the pair, clarified the theorem comment, and checked it for this task.

The theorem `Langlands.Global.cmCharacterGlobalization.{u,v}` proves the
unchanged Library proposition
`Langlands.Global.CMCharacterGlobalizationStatement.{u,v}` from
`Langlands.Global.Arithmetic.CMCharacterStatement`. That proposition is the
conjunction of four statements. The proof supplies each conjunct from
published theorems:

1. `CMUnramifiedInfinityRealizationStatement.{u}` is
   `cmUnramifiedInfinityRealization.{u}` (module
   `Langlands.Global.Arithmetic.CMUnramifiedInfinityProof`).
2. `CMFiniteCharacterPrescriptionStatement.{u}` is
   `cmFiniteCharacterPrescriptionOfFiniteOrder.{u}` (module
   `Langlands.Global.Arithmetic.CMFiniteCharacterPrescriptionReductionProof`)
   applied to `finiteOrderCharacterPrescription_proof.{u}` (module
   `Langlands.Global.Arithmetic.CharacterPrescriptionProof`).
3. `IntegralUnitCharacterExtensionStatement.{u}` is
   `integralUnitCharacterExtension.{u}` (module
   `Langlands.Global.Arithmetic.IntegralUnitCharacterExtensionProof`).
4. `CMRegularUnitPrescriptionStatement.{u,v}` is
   `cmRegularUnitPrescriptionOfInputs.{u,v}` (module
   `Langlands.Global.Arithmetic.CMCharacterAssemblyProof`) applied to the
   terms of items 1, 2 and 3.

The anonymous-constructor term builds the conjunction directly and keeps the
independent universes `u` and `v`. It adds no definitions or hypotheses. The
auxiliary local norm-stabilizer construction mentioned in the statement's
documentation is not part of this proposition.
