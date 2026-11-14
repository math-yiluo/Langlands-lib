# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof`

`Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Vanishing of nonconjugating geometric pieces for associated Levis.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetVanishingHelpers`

## Declarations

- `Langlands.AllField.CuspidalSupport.associatedGeometricPieceVanishing` (theorem): The published vanishing component, for every rank including zero.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.finiteAutomorphismOrbit_eq_of_le`, `Langlands.CuspidalSupport.conjugatesLevi_of_le_of_associated`, `Langlands.CuspidalSupport.source_refinement_proper_of_associated_nonconjugating`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
