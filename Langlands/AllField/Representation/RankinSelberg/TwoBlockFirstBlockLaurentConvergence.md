# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Spectral series of the original and transformed small integrals**

For representations of full Whittaker type and nonzero functionals, the actual
unequal-rank integral of every pair of coefficient-image vectors converges absolutely on
a right half-plane, by the published unequal-rank analytic theorem; there it is the
absolutely summable series of its determinant-slice coefficients. The transformed
integral is the same object for the inverse-transpose pair, the inverse additive
character and the exchanged blocks.

## Imports from the port

- `Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.Geometric.GeometricLemmaStatement`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.NormalizedCompactIntegrationProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSlices`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`
- `Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.unequalRankSliceCoefficientAt` (def): The slice coefficient at a fixed large rank, with the rank equality transporting
  only types.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.smallIntegral_series` (theorem): The actual small integral of coefficient-image vectors is, on a right half-plane, the
  absolutely summable series of its slice coefficients.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.dualSmallIntegral_series` (theorem): The actual transformed small integral is, on a right half-plane, the absolutely
  summable series of the slice coefficients of the inverse-transpose pair.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.unequalRankIntegrandAt` (def): The unequal-rank integrand at a fixed large rank, with the rank equality transporting
  only types.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.smallIntegrand_integrableOn_slice` (theorem): On every determinant slice, the inner rectangular integral at `s = 0` of the actual
  small integrand of coefficient-image vectors is integrable.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.dualIntegrand_integrableOn_slice` (theorem): On every determinant slice, the inner integral at `s = 0` of the actual transformed
  small integrand is integrable.
