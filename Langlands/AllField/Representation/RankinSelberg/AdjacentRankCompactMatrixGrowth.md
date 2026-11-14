# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixGrowth`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactMatrixGrowth` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixGrowth`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixGrowth` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.uniformizer_pow_ord_div_mem` (theorem): A determinant denominator is cleared by its nonnegative integral order.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.isEntryBounded_of_scaled_integral` (theorem): Clearing entries and then the determinant clears inverse entries as well.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.exists_scaled_integral_of_isCompact` (theorem): A single uniformizer power makes every entry in a compact matrix set integral.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.pow_ord_mul_abs_pow_le` (theorem): The nonnegative determinant order contributes at most a fixed determinant pole.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.exists_coefficient_det_growth` (theorem): One determinant-pole order works before all coefficient vectors and all compact
  matrix sets, for evaluation at the inverse matrix.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.coefficientDeterminantOrder` (def): A determinant-pole order chosen before the coefficient vector and compact set.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.coefficientDeterminantOrder_spec` (theorem).
