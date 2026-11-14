# All-field port of `Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary`

`Langlands.AllField.Representation.Whittaker.MirabolicPairingRigidityElementary` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Elementary cases of mirabolic twisted pairing rigidity**

For an irreducible representation of the mirabolic group, the radical either
acts trivially or the vectors `ξ u x - x` span the whole space. This module
proves the rank-one case and the cases in which at least one representation has
trivial radical action. Only the case of two radical-generated representations
remains, recorded as `RadicalGeneratedPairingRigidity`.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatementSupplement`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicRigidity.RadicalGeneratedPairingRigidity` (def): The remaining case of `MirabolicTwistedPairingRigidityStatement`: both
  representations are radical-generated.
- `Langlands.AllField.Whittaker.MirabolicRigidity.mirabolicTwistedPairingRigidity_of_radicalGenerated` (theorem): Rigidity follows from its radical-generated case.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicRigidity.IsRadicalTrivial`, `Langlands.Whittaker.MirabolicRigidity.IsRadicalGenerated`, `Langlands.Whittaker.MirabolicRigidity.radicalSpan`, `Langlands.Whittaker.MirabolicRigidity.radicalTrivial_or_radicalGenerated`, `Langlands.Whittaker.MirabolicRigidity.forms_eq_zero_of_trivial_of_generated`, `Langlands.Whittaker.MirabolicRigidity.forms_eq_zero_of_generated_of_trivial`, `Langlands.Whittaker.MirabolicRigidity.determinantWeight_radical`, `Langlands.Whittaker.MirabolicRigidity.apply_eq_self_of_subsingleton`, `Langlands.Whittaker.MirabolicRigidity.equivOfSubsingleton`, `Langlands.Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible`, `Langlands.Whittaker.MirabolicRigidity.nonempty_linearEquiv_of_subsingleton`, `Langlands.Whittaker.MirabolicRigidity.rankOneEval`, `Langlands.Whittaker.MirabolicRigidity.rankOneConstant`, `Langlands.Whittaker.MirabolicRigidity.rankOneEval_bijective`, `Langlands.Whittaker.MirabolicRigidity.rankOne_equiv`, `Langlands.Whittaker.MirabolicRigidity.exists_scalar_of_commute`, `Langlands.Whittaker.MirabolicRigidity.rank_le_aleph0`, `Langlands.Whittaker.MirabolicRigidity.leviScalar`, `Langlands.Whittaker.MirabolicRigidity.leviScalar_commutator_mem`, `Langlands.Whittaker.MirabolicRigidity.apply_mul_leviScalar`, `Langlands.Whittaker.MirabolicRigidity.det_leviScalar`, `Langlands.Whittaker.MirabolicRigidity.determinantWeight_leviScalar`, `Langlands.Whittaker.MirabolicRigidity.exists_finset_of_radicalTrivial`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
