# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalCoefficientTests`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalCoefficientTests` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalCoefficientTests`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalCoefficientTests` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact determinant-unit coefficients of supercuspidal representations**

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.CuspidalityComparisonProof`
- `Langlands.AllField.Representation.CuspidalSupport.HarishChandraAssembly`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.Geometric.GeometricLemmaStatement`

## Declarations

- `Langlands.AllField.GodementJacquet.oneBlockDeterminantUnitHomeomorph` (def): The determinant-unit subgroup of the positive one-block Levi is the
  actual determinant-unit subgroup of GL, with its induced topology.
- `Langlands.AllField.GodementJacquet.hasCompactSupport_determinantUnit_coefficient` (theorem): The published product-Levi Harish-Chandra theorem implies compact
  support for every smooth-dual supercuspidal coefficient on `|det| = 1`.
