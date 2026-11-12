# Proof of `Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement`

This module proves the published proposition `Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement` (module `Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement`) at every universe `u`. The statement says that for a connected reductive group over a field, a maximal split torus `i : T ⟶ G` and a cocharacter `ζ` of `T`, with the represented dynamic subgroups and Lie coordinates of the statement, the determinant characters of `Z(ζ)` on `Lie U(ζ)` and on `Lie U(−ζ)` sum to zero.

The theorem is `Langlands.GroupScheme.Dynamic.leviAdjointDeterminantReciprocity : LeviAdjointDeterminantReciprocityStatement.{u}`, with no hypotheses.

## Proof

The proof term is the published reduction `leviAdjointDeterminantReciprocity_of_structure` applied to the published proofs `relativeRootReflectionExistence`, `centralSplitTorusCharacter` and `dynamicCentralizerReductive` of its three hypotheses.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.leviAdjointDeterminantReciprocity_of_structure` (module `Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction`)
- `Langlands.GroupScheme.relativeRootReflectionExistence` (module `Langlands.GroupScheme.Rational.RootReflectionExistenceProof`)
- `Langlands.GroupScheme.centralSplitTorusCharacter` (module `Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof`)
- `Langlands.GroupScheme.dynamicCentralizerReductive` (module `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`)
