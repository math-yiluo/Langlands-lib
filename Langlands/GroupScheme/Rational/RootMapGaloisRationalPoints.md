# Galois transport of rational values of compatible root maps

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.RootMapGaloisRationalPoints`.

## Statement

Let `k ⊆ K` be fields, `G` an affine group scheme over `Spec k`, and `p` a split pinning of
the base change `G_K`. Let `x : p.NormalizedSimpleRootParametrizations` be normalized
simple-root maps and `ρ` an action of `Aut_k(K)` on the simple roots. Suppose `x` is
compatible with `ρ` in the sense of the published predicate
`SplitPinning.RootMapsGaloisCompatible k K p x ρ` (module `Rational.SteinbergRootProduct`).

`SplitPinning.RootMapsGaloisCompatible.rationalPoint hx σ a c` states that coefficient
conjugation by `σ` (`GaloisPointComparison.rationalConjugate`) carries the rational root
point `x_a(c)` to `x_{ρ σ a}(σ c)`. Here `x_a(c)` is
`(x a).toRootParametrization.rationalPoint c`.

## Proof

This is the published theorem `SplitPinning.RootMapsGaloisCompatible.rationalPoints` of module
`Rational.SteinbergRationalGaloisTransport`, which takes `x` and `ρ` explicitly. The present
theorem is a wrapper with `x` and `ρ` implicit, kept because downstream modules
(`NegativeRootPartnerGalois`, `OrthogonalOrbitCorootWords`) use this interface.

An earlier version of this module reproved the two evaluation helpers
`PolynomialGalois.aeval_comp_conjugate` and
`NormalizedRootParametrization.coefficientCurve_evaluate_rationalPoint`. These have the same
fully qualified names as declarations of `SteinbergRationalGaloisTransport`, so the two
modules could not be imported together. This version removes the duplicates and imports the
published module instead.

## Provenance

Internal interface wrapper; no new mathematical assertion.
