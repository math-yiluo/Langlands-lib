# Galois transport of rational values of compatible root maps

Author: Worker 4348.

Let `k ⊆ K` be fields in one universe, `G` an affine group scheme over `k`, and
`p` a split pinning of `G_K`. Whole-map compatibility of normalized simple-root
maps `x` with a Galois action `ρ` gives
`rationalConjugate σ (x_a(c)) = x_{ρ σ a}(σ c)` for every rational coordinate `c`.

This module reuses the published
[SteinbergRationalGaloisTransport](SteinbergRationalGaloisTransport.md) module.
Its `PolynomialGalois.aeval_comp_conjugate` and
`NormalizedRootParametrization.coefficientCurve_evaluate_rationalPoint` supply
the polynomial-evaluation comparisons. The exported
`SplitPinning.RootMapsGaloisCompatible.rationalPoint` is the same result as
`RootMapsGaloisCompatible.rationalPoints`, with the root-map family and the
permutation action implicit. Its proof applies that existing theorem.

This is an internal interface for the published whole-map compatibility result.
