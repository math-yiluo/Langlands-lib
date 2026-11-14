# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof`

`Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The individual-piece reduction of BZ77 2.13(c), assembled from its three
published components.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof`
- `Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof`
- `Langlands.AllField.Representation.CuspidalSupport.MinimalWeylTransportProof`

## Declarations

- `Langlands.AllField.CuspidalSupport.padicAssociatedGeometricPieces` (theorem): BZ77 2.13(c) individual-piece reduction: for every prime, `p`-adic field,
  compatible topology and positive rank, nonconjugating pieces vanish,
  conjugating pieces are whole-Levi transports, and minimal transport preserves
  quasicuspidality.
