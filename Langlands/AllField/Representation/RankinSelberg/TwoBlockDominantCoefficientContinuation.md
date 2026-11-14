# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual model coefficient clearing and denominator bounds**

Convergence is taken from the actual intrinsic zeta-value witnesses. Full
Whittaker type identifies those coefficients with any fixed nonzero models.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankClearedContinuation`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankDeterminantSlices`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.EqualModelFiniteClearing` (def): Every pair of coefficients in the fixed models, with every actual row
  test, has a finite numerator for the specified ordinary clearing polynomial.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.equalRank_hasBilateralSpectralExpansion` (theorem): The actual equal-rank coefficient expansion on a right half-plane.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.equalModelFiniteClearing_polynomialDivisibility` (theorem): Finite clearing on one nonzero model pair controls every intrinsic equal
  rank zeta value and yields the required polynomial divisibility direction.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.StrictModelFiniteClearing` (def): The actual unequal-rank determinant coefficients in the specified models
  have finite numerators after multiplying by the given polynomial.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.unequalRank_hasBilateralSpectralExpansion` (theorem): Product-space absolute convergence gives the actual unequal-rank spectral
  expansion on that same right half-plane.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictModelFiniteClearing_polynomialDivisibility` (theorem): A uniform finite clearing on fixed nonzero models controls the complete
  intrinsic unequal-rank L polynomial. No new convergence assumption is needed.
