# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalCutoffTests`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffTests` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalCutoffTests`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalCutoffTests` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual determinant-unit cutoff matrix tests**

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalCoefficientTests`
- `Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof`

## Declarations

- `Langlands.AllField.GodementJacquet.determinantUnitTestToMatrixTest` (def): Extend a test on the determinant-unit subgroup by zero directly into the
  full matrix space, using its actual open embedding.
- `Langlands.AllField.GodementJacquet.determinantUnitTestToMatrixTest_apply` (theorem).
- `Langlands.AllField.GodementJacquet.determinantUnitTestToMatrixTest_eq_zero` (theorem).
- `Langlands.AllField.GodementJacquet.supercuspidalDeterminantUnitCoefficient` (def): The genuine compact coefficient on the determinant-unit subgroup, linear
  in the representation vector.
- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest` (def): The coefficient is cut off to determinant norm one and extended by zero
  to singular matrices and to every other determinant shell.
- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest_apply` (theorem).
- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest_apply_of_not_mem` (theorem).
- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest_singular` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.tsupport_determinantUnitTestToMatrixTest_subset`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
