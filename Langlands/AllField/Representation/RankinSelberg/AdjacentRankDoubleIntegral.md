# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankDoubleIntegral`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankDoubleIntegral` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankDoubleIntegral`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankDoubleIntegral` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactMatrixConvergence`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integrand` (def): The literal JPSS double-integral scalar kernel, after absorbing a fixed
  ambient group element into the rectangular test.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.columnHomeomorph` (def): Multiplication by an invertible matrix on column space.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.columnHomeomorph_apply` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.rowMeasure_map_mulVec` (theorem): The supplied row Haar scales by the reciprocal normalized determinant
  under multiplication by the matrix on columns.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integral_mulVec` (theorem): Exact Bochner change of variables, retaining the supplied Haar normalization.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.fiberNorm` (def): The integral of the absolute value of a last-column slice, as an actual
  complex square-matrix Schwartz--Bruhat function.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.fiberNorm_apply` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.norm_fiberNorm_apply` (theorem): The slice-norm value is a nonnegative real number.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.jacobian_detWeight` (theorem): The column Jacobian reduces the exact half-modulus by one.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.continuous_integrand` (theorem): Continuity of the literal two-variable kernel requires only smoothness.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integrable_column` (theorem): Every fixed-matrix column section is integrable, without a twist restriction.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integral_norm_column` (theorem): Exact reduction of the integrated column norm to the square-matrix norm.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integral_column_partialFourier` (theorem): Column integration is exactly inverse-character partial Fourier evaluation
  at the actual adjacent-rank kernel matrix.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integrable_realTwist` (theorem): Absolute convergence on the actual product measure above the uniform
  square-matrix threshold.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.double_integral_eq_partialFourier` (theorem): Fubini and the exact column Fourier identity identify the literal JPSS
  iterated integral with the partial-Fourier model integral.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.double_integral_eq_modelIntegrand` (theorem): At an arbitrary ambient group element, the literal translated double integral
  is the integral of the published actual tensor-model integrand.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.double_integral_eq_modelIntegral` (theorem): Including the exact ambient character and modulus gives the published
  adjacent-rank model integral itself.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.AdjacentDoubleIntegral.integrable_comp_mulVec`, `Langlands.RankinSelberg.AdjacentDoubleIntegral.normTest`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
