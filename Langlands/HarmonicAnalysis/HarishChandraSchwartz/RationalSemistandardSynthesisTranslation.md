# Translation of the actual semistandard synthesis

`WeightedSynthesisTranslationStatement` expresses the product-group
equivariance of the source-weighted synthesis on the actual finite-support
smooth spectral carrier. The action on functions has pointwise formula
`f(x₂⁻¹ * g * x₁)`. On the spectral side the action is the published
normalized product-induced action at each representation.

The proof applies the actual orbit coefficient translation law under
the normalized packet integral. The action preserves the literal support
of the input family, so both source-weighted sums use the same indices
and coefficients. The calculation uses the existing scalar and measure
inputs to `weightedSynthesis`. It applies in particular to the smooth
proper Fourier lift and supplies the synthesis comparison for the
translation of the VIII.2 subtraction. The field and representation
carrier universes are independent.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, Journal of the Institute of Mathematics of
Jussieu 2 (2003), I.6, VI.3 and VIII.2.
[DOI](https://doi.org/10.1017/S1474748003000082)
