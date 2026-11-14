# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankDeterminantSlices`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankDeterminantSlices` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankDeterminantSlices`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankDeterminantSlices` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Determinant coefficients of the actual unequal-rank integral**

Internal consequences of the published unequal-rank integrand, normalized
determinant weight and quotient determinant-slice partition. The expansion
requires genuine integrability and asserts no support or continuation result.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticBridge`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankSliceExpansionProof`
- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.unequalRankAverage` (def): Integrate the actual rectangular variable first, with its supplied measure.
- `Langlands.AllField.RankinSelberg.unequalRankSliceCoefficient` (def): Actual unequal-rank coefficient series, with the rank-normalizing weight
  already included by evaluating the integrand at the spectral parameter zero.
- `Langlands.AllField.RankinSelberg.unequalRankIntegrand_eq_mul_spectralPoint_zpow` (theorem): The spectral factor depends only on the determinant slice and is independent
  of the rectangular variable.
- `Langlands.AllField.RankinSelberg.unequalRankAverage_eq_mul_spectralPoint_zpow` (theorem): Rectangle integration retains the same exact slice spectral factor, even for
  totalized integrals outside integrability.
- `Langlands.AllField.RankinSelberg.setIntegral_unequalRankAverage_determinantSlice` (theorem): The actual restricted iterated integral is its coefficient at zero times the
  spectral factor. No Fubini exchange or convergence assertion is involved.
- `Langlands.AllField.RankinSelberg.sliceIntegrableAt_unequalRankAverage_iff` (theorem): Genuine integrability of the rectangle average on a determinant slice is
  independent of the spectral parameter.
- `Langlands.AllField.RankinSelberg.unequalRankSliceExpansion` (theorem): At a genuinely integrable parameter the iterated unequal-rank integral is the
  absolutely summable series of its actual determinant coefficients.
- `Langlands.AllField.RankinSelberg.unequalRankSliceExpansion_of_converges` (theorem): Actual product-space absolute convergence supplies the averaged integrability
  needed for the coefficient expansion. Only the inner measure needs `SFinite`.
