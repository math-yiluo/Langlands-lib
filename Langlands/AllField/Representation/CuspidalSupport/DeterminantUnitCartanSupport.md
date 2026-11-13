# All-field port of `Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport`

`Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitCartanSupport` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.DeterminantUnit`
- `Langlands.AllField.Representation.Geometric.RefinementFunctors`
- `Langlands.AllField.Representation.Jacquet.Parabolic`

## Declarations

- `Langlands.AllField.CuspidalSupport.LeviAdmissibility.block_sums_eq_zero_of_determinantUnit_cartan` (theorem): The actual residue-normalized determinant-unit condition forces zero sums
  in every block of a product Cartan factorization.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.LeviAdmissibility.finite_zeroSum_boundedGap`, `Langlands.CuspidalSupport.LeviAdmissibility.valuation_det_integralRange`, `Langlands.CuspidalSupport.LeviAdmissibility.determinant_torus`, `Langlands.CuspidalSupport.LeviAdmissibility.sum_eq_zero_of_cartan`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
