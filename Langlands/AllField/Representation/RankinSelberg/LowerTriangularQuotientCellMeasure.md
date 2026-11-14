# All-field port of `Langlands.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure`

`Langlands.AllField.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Quotient measures on the open lower-triangular cell**

A right-invariant quotient measure on `N_m \ GL_m` that is finite on compacts
pulls back along the open cell `B⁻_m → N_m \ GL_m` to a right-invariant measure on
`B⁻_m`, finite on compacts, whose pushforward recovers the quotient measure when
the cell is conull. Nonzero right-invariant measures finite on compacts on a
second countable locally compact group differ by a positive scalar.

## Imports from the port

- `Langlands.AllField.Group.GL.LowerTriangularQuotientCell`
- `Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport`

## Declarations

- `Langlands.AllField.RankinSelberg.lowerTriangularQuotientMap_mul` (theorem): The cell map intertwines right multiplication in `B⁻_m` with right
  translation of cosets.
- `Langlands.AllField.RankinSelberg.lowerTriangularQuotientMap_measurableEmbedding` (theorem): The cell map is a measurable embedding for the Borel structures.
- `Langlands.AllField.RankinSelberg.comap_lowerTriangularQuotientMap_properties` (theorem): Pullback of a right-invariant quotient measure, finite on compacts, to the
  lower triangular group: it is right invariant and finite on compacts, and when
  the cell is conull its pushforward is the quotient measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.exists_pos_smul_eq_of_isMulRightInvariant`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
