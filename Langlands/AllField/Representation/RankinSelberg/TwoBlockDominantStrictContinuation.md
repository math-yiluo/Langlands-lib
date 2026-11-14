# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictContinuation`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictContinuation` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictContinuation`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictContinuation` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictCoefficients`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictRectangleMeasure_sigmaFinite` (instance): The supplied rectangle product remains sigma-finite under the canonical
  Borel measurable-space identification.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictRankAnalyticAt` (theorem): Published unequal-rank analysis for the exact supplied Haar rectangle,
  transporting only its measurable-space presentation.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictIntegral_eq` (theorem): The fixed-rank Borel rectangle integral is exactly the original supplied
  product-Haar integral.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictCoefficient_continuationData` (theorem): The actual strict coefficients expand the original supplied-Haar integral
  on a right half-plane; the same integral has a rational continuation.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictCoefficient_polynomialDivisibility` (theorem): Uniform clearing of the actual fixed-rank coefficients controls the
  intrinsic normalized generator for the original supplied product measure.
