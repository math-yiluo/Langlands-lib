# All-field port of `Langlands.Representation.Geometric.StandardIntersectionsProof`

`Langlands.AllField.Representation.Geometric.StandardIntersectionsProof` is the all-field port of the Library module `Langlands.Representation.Geometric.StandardIntersectionsProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.Geometric.StandardIntersectionsProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.Geometric.WeylStatementSupplement`

## Declarations

- `Langlands.AllField.Geometric.padicStandardIntersectionsTheorem` (theorem): The exact published two-sided p-adic standard-intersection statement.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.index_blockIndex`, `Langlands.Geometric.index_ne_of_block_ne`, `Langlands.Geometric.mem_parabolic_iff_blockIndex`, `Langlands.Geometric.mem_unipotent_iff_blockIndex`, `Langlands.Geometric.conjugatedLeviMap_entry`, `Langlands.Geometric.conjugatedLeviMap_zero_iff`, `Langlands.Geometric.conjugatedLeviMap_identity_iff`, `Langlands.Geometric.mem_sourceParabolic_iff`, `Langlands.Geometric.mem_sourceLevi_iff`, `Langlands.Geometric.mem_sourceUnipotent_iff`, `Langlands.Geometric.standardIntersections_of_comparisons`, `Langlands.Geometric.exists_standardIntersections`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
