# All-field supplement to `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement`

`Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement` supplements the Library module `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement`, the existing all-field port of `Langlands.Representation.Parabolic.NormalizedJacquetStatement`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.NormalizedJacquetStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement`

## Declarations

- `Langlands.AllField.Parabolic.NormalizedJacquetExactnessClause` (def): The normalized quotient intertwiners preserve all three parts of a short
  exact sequence of smooth ambient representations.

Declarations of the original re-declared by `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement` and therefore not here: `Langlands.Parabolic.NormalizedJacquetAdmissibilityClause`.

Public declarations of the original that are not re-declared here: `Langlands.Parabolic.NormalizedJacquetSmoothnessClause`, `Langlands.Parabolic.NormalizedFrobeniusClause`, `Langlands.Parabolic.NormalizedJacquetStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
