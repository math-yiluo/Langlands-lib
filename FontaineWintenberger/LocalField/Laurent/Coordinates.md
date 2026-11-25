# Laurent series coordinates from a coefficient ring map and a uniformizer

Module `FontaineWintenberger.LocalField.Laurent.Coordinates`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file proves that a complete discrete valuation ring `R` equipped with a ring homomorphism from a field `k` that induces an isomorphism onto the residue field is a power series ring over `k`, and that its fraction field is the Laurent series field.

## Complete discrete valuation rings

Data: a field `k`, a discrete valuation ring `R`, a ring homomorphism `c : k →+* R`, an isomorphism `e : k ≃+* ResidueField R` with `residue (c a) = e a`, and an irreducible `π`.

- `residueDigit`, `residueQuotient`, `residueRemainder`, `residueExpansion`: the digit of `x` is `e⁻¹` of its residue; subtracting `c` of the digit and dividing by `π` gives the next remainder; the digits form a power series over `k`. `residueExpansion_remainder` gives the finite expansion with its remainder.

Assume further that `k` is discrete, `R` is a complete Hausdorff topological ring with linear topology, and `π` is topologically nilpotent (`PowerSeries.HasEval π`).

- `powerSeries_eval₂_surjective`, `powerSeries_eval₂_injective`: evaluation `PowerSeries.eval₂ c π` is bijective.
- `powerSeriesUniformizerEquiv : PowerSeries k ≃+* R`: the resulting isomorphism. It sends constants to `c a` and `X` to `π`, is continuous, and is the only continuous ring homomorphism with these values (`powerSeriesUniformizerEquiv_unique`).

## Valued fields

Let `F` be a field with `Valued F ℤᵐ⁰`, valuation `v` and valuation ring `𝒪`.

- Instances: `𝒪` is a topological ring, a uniform additive group, has a linear topology, and is complete when `F` is.
- For `π ∈ 𝒪` with `v π = exp(−1)`: `π` is topologically nilpotent (`hasEval_of_valuation_exp_neg_one`) and generates the maximal ideal; `𝒪` is a discrete valuation ring (`valuationSubring_isDiscreteValuationRing_of_uniformizer`) in which `π` is irreducible.

For `F` complete, with `c`, `e` as above for `R = 𝒪`:

- `valuedPowerSeriesEquiv : PowerSeries k ≃+* 𝒪`; by `valuation_valuedPowerSeriesEquiv` a nonzero `f` goes to an element of valuation `exp(−order f)`.
- `laurentUniformizerEquiv : LaurentSeries k ≃+* F`: its extension to fraction fields, sending constants to `c a` and `X` to `π`.
- `valuation_laurentUniformizerEquiv`: it carries the `X`-adic valuation of `LaurentSeries k` to `v`; it and its inverse are uniformly continuous.
- `laurentUniformizerEquiv_unique`: a continuous ring homomorphism `LaurentSeries k → F` with the same values on constants and on `X` equals it.

## Proofs

Surjectivity is the convergence of the digit expansion; injectivity comes from factoring a nonzero series as `X^order` times a unit. Uniqueness uses density of polynomials in power series and of rational functions in Laurent series.

## Points to watch

- The coefficient map `c` is a hypothesis: the file does not construct a coefficient field.
- `residueQuotient` is defined by `choose`.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Laurent/Coordinates.lean` (SHA-256 of the source file `0fa6b0911ebc533079419e331f5f672b8d97b081c9c7317931dc2e1edc09ab1f`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
