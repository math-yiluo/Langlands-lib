# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixSupport` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact scalar support of actual supercuspidal coefficient spans**

## Imports from the port

- `Langlands.AllField.Group.GL.UnramifiedCharacterSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitStructureProof`
- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalCoefficientTests`
- `Langlands.AllField.Representation.GodementJacquet.Zeta`

## Declarations

- `Langlands.AllField.GodementJacquet.determinantNorm_ker_sup_center_finiteIndex` (theorem): The GL determinant-unit subgroup has finite index after adjoining the
  center, by the published one-block product-Levi result.
- `Langlands.AllField.GodementJacquet.exists_centralCharacter_compactScalarSupport` (theorem): Irreducible supercuspidality supplies the actual scalar character and
  compact scalar covers for every bi-smooth coefficient, including finite sums.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.centralCovariantFunctions`, `Langlands.GodementJacquet.biSmoothMatrixCoefficients_le_centralCovariantFunctions`, `Langlands.GodementJacquet.continuous_of_mem_biSmoothMatrixCoefficients`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
