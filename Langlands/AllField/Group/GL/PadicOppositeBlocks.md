# All-field port of `Langlands.Group.GL.PadicOppositeBlocks`

`Langlands.AllField.Group.GL.PadicOppositeBlocks` is the all-field port of the Library module `Langlands.Group.GL.PadicOppositeBlocks`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Group.GL.PadicOppositeBlocks` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Group.GL.PadicBlocksSupplement`

## Declarations

- `Langlands.LocalFieldData.oppositeBlockLeviProjection` (def): The continuous actual lower-block projection into the common Levi.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.oppositeUnipotentRadicalTopology`, `Langlands.PadicField.TopologicalData.oppositeUnipotentRadicalTopologicalGroup`, `Langlands.PadicField.TopologicalData.oppositeUnipotentRadicalT2Space`, `Langlands.PadicField.TopologicalData.oppositeUnipotentRadicalLocallyCompactSpace`, `Langlands.PadicField.TopologicalData.oppositeBlockLeviSection`, `Langlands.PadicField.TopologicalData.oppositeBlockDecomposition`, `Langlands.PadicField.TopologicalData.oppositeBlockLeviActionContinuous`, `Langlands.PadicField.canonicalOppositeUnipotentRadicalTopology`, `Langlands.PadicField.canonicalOppositeUnipotentRadicalTopologicalGroup`, `Langlands.PadicField.canonicalOppositeUnipotentRadicalT2Space`, `Langlands.PadicField.canonicalOppositeUnipotentRadicalLocallyCompactSpace`, `Langlands.PadicField.canonicalOppositeBlockLeviProjection`, `Langlands.PadicField.canonicalOppositeBlockLeviSection`, `Langlands.PadicField.canonicalOppositeBlockDecomposition`, `Langlands.PadicField.canonicalOppositeBlockLeviActionContinuous`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
