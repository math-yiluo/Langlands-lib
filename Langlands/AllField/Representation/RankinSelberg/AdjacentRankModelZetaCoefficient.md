# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankModelZetaCoefficient`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelZetaCoefficient` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankModelZetaCoefficient`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankModelZetaCoefficient` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The actual model substitution preceding the finite convolution in JPSS 6.3.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankShellConvolution`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticBridge`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.adjacentRankInnerMultiplier_mul` (theorem).
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankSeparatedTest_rho0_rankInclusion` (theorem): The proved elementary Fourier covariance evaluates the separated test
  at precisely the square block `h g` and the last row of `h⁻¹`.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral_separated_rankInclusion_raw` (theorem): Direct substitution of a separated pure tensor into the literal model.
  No Whittaker image or spanning assertion is assumed.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral_separated_rankInclusion_weighted` (theorem): Right substitution in the same GL Haar measure and cancellation of the
  two half-weights give the kernel used in the shell convolution.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankModel_corankOneSlice_eq_before` (theorem): A Whittaker function realized by this separated model has exactly the
  before-shear kernel on each determinant slice. Realization is explicit data.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.adjacentRankSeparatedTest`, `Langlands.RankinSelberg.adjacentRankSeparatedTest_join`, `Langlands.RankinSelberg.Padic.adjacentRankModel_corankOne_finiteConvolution`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
