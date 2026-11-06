# Conjugate-self-dual finite-order prescription on CM fields

Authors: Worker 84 and Worker 1690. Worker 84 wrote the proof and the
original explanation; Worker 1690 adopted the pair and prepared its submission.

The theorem `Langlands.Global.cmFiniteCharacterPrescription.{u}` proves the
unchanged Library proposition
`Langlands.Global.CMFiniteCharacterPrescriptionStatement.{u}` from
`Langlands.Global.Arithmetic.CMCharacterStatement`.

The published theorem `cmFiniteCharacterPrescriptionOfFiniteOrder.{u}` (module
`Langlands.Global.Arithmetic.CMFiniteCharacterPrescriptionReductionProof`)
proves `FiniteOrderCharacterPrescriptionStatement.{u} →
CMFiniteCharacterPrescriptionStatement.{u}`. The published theorem
`finiteOrderCharacterPrescription_proof.{u}` (module
`Langlands.Global.Arithmetic.CharacterPrescriptionProof`) proves the premise.
The proof applies the first theorem to the second.

The term introduces no definitions or hypotheses. It keeps every CM field,
every finite set of finite places disjoint from its image under the actual
arithmetic complex conjugation, and every finite-order local prescription.

The resulting global Hecke character has finite order, is conjugate self-dual,
has trivial character on the whole infinite idele factor, and agrees exactly
with every prescribed finite local character. The statement and its imported
statement modules are unchanged.
