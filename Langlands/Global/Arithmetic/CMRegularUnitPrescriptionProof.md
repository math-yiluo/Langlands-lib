# Regular CM infinity type with prescribed unit components

Author: Worker 84, who wrote the proof and this explanation.

The theorem `Langlands.Global.cmRegularUnitPrescription.{u,v}` proves the
unchanged Library proposition
`Langlands.Global.CMRegularUnitPrescriptionStatement.{u,v}` from
`Langlands.Global.Arithmetic.CMCharacterStatement`.

The published theorem `cmRegularUnitPrescriptionOfInputs.{u,v}` (module
`Langlands.Global.Arithmetic.CMCharacterAssemblyProof`) proves
`CMUnramifiedInfinityRealizationStatement.{u} →
CMFiniteCharacterPrescriptionStatement.{u} →
IntegralUnitCharacterExtensionStatement.{u} →
CMRegularUnitPrescriptionStatement.{u,v}`. The proof discharges its three
premises with published theorems:

- `cmUnramifiedInfinityRealization.{u}` (module
  `Langlands.Global.Arithmetic.CMUnramifiedInfinityProof`);
- `cmFiniteCharacterPrescriptionOfFiniteOrder.{u}` applied to
  `finiteOrderCharacterPrescription_proof.{u}` (modules
  `Langlands.Global.Arithmetic.CMFiniteCharacterPrescriptionReductionProof`
  and `Langlands.Global.Arithmetic.CharacterPrescriptionProof`);
- `integralUnitCharacterExtension.{u}` (module
  `Langlands.Global.Arithmetic.IntegralUnitCharacterExtensionProof`).

The field universe `u` and the imaginary-quadratic universe `v` remain
independent, as in the target. The term introduces no definitions or
hypotheses, and every quantifier of the statement is kept.
