# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Upper determinant-slice analysis for the dominant first-block identity**

Internal consequences of the ordinary Jacquet convergence and realization,
the unequal-rank finite expansion, and the JPSS unequal-rank analytic theorem.

## Imports from the port

- `Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement`
- `Langlands.AllField.Representation.RankinSelberg.NormalizedCompactIntegrationProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantJacquetSeries`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankDeterminantSlices`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.rectangularBorelMeasure` (def): The supplied finite product Haar measure in the Borel measurable structure
  used by the determinant coefficient API.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.integrable_rectangularBorelMeasure` (theorem): Transport Schwartz integrability along equality of the product and Borel
  measurable structures, without a measure map or rescaling.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.exists_uniformOrdinaryJacquetRealization` (theorem): One ordinary Jacquet realization, including zero supplied block functionals,
  chosen before all quotient measures and tests.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.continuous_diagonalIntegrand` (theorem): The diagonal term of the finite rectangular expansion is continuous,
  with the full original rank-gap exponent.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.continuous_upperAverage` (theorem): Finite Schwartz expansion gives a continuous rectangle average for every
  spectral parameter, independently of outer convergence.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.UpperSliceConverges` (def): Upper product-space convergence on every determinant slice.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.upperSliceConverges` (theorem): Restrict right-half-plane convergence to a slice and divide by its nonzero
  constant spectral weight. This retains zero supplied functionals.
