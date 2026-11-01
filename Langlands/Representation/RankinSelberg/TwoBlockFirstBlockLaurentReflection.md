# Reflection of the polynomial-cleared small functional equation

This derived internal algebra supports the first-block calculation in Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions* (1983), Section 4.9,
printed pages 416–418, using the bilateral-series convention of Section 4.1,
printed page 406. It concerns the actual finite Laurent action from
`Langlands.HarmonicAnalysis.BilateralLaurentSeries`.

For a positive integer `q`, `reflectLaurent q hq` substitutes
`X ↦ q⁻¹ X⁻¹` in a finite Laurent polynomial. Its monomial formula is
`c Xᵏ ↦ c q⁻ᵏ X⁻ᵏ`. The construction uses the additive group of integer
exponents and the universal algebra map of its monoid algebra.

`reflectSeries q a` has coefficient `qⁿ a(-n)`. The theorem
`reflectSeries_laurent_smul` proves that this coefficient operation intertwines
the actual finite convolution with `reflectLaurent`. Its proof uses additivity
and the integer-power identity on monomials. `reflectLaurent_toLaurent` identifies
the reflection of an ordinary polynomial with the exact `reflectedPolynomial`
defined in the companion algebra module.

`reflectSeries_ofLaurentPolynomial` identifies the reflected finite coefficient
series with the coefficient embedding of the reflected Laurent polynomial.
`laurentEval_reflectLaurent` checks that this substitution corresponds to the
actual change `s ↦ 1-s` of the spectral parameter.

`laurent_eq_of_infinite_spectral_eval_eq` proves finite Laurent uniqueness by
embedding into rational functions and applying rational-function uniqueness on
the image of an infinite set of real parameters. For `q > 1`, this image is
infinite because the real spectral parametrization is injective.

`normalizedFE_cleared_laurent_identity` assumes actual finite lifts
`laurentToRatFunc L = P R` and `laurentToRatFunc Ld = Pdual Rd`, together with the
published `NormalizedFunctionalEquation`. It proves

```text
reflectLaurent q hq Ld = C (ζ^e c) * T d * L.
```

The proof removes the finitely many real parameters at which either original
rational denominator vanishes, evaluates both finite lifts, applies the
supplied functional equation there, and invokes finite Laurent uniqueness.
It does not assume the dual and original series converge on a common
half-plane.

`normalizedFE_coefficient_identity_of_cleared` additionally assumes
`P.toLaurent • a = ofLaurentPolynomial L` and the analogous dual equality. It
reflects the latter equality, uses the finite identity just proved, and obtains

```text
reflectedPolynomial q Pdual • (fun n => q^n * ad (-n))
  = (C (ζ^e c) * T d * P.toLaurent) • a.
```

These assumptions explicitly retain the analytic obligation to identify each
cleared coefficient series with its own finite lift.

`coeffwiseIntegral_congr_ae` transfers almost-everywhere equality to all
coefficient integrals. `integral_laurent_identity_ae` combines this with
commutation of finite Laurent multiplication and coefficientwise integration.
Only integrability of each input coefficient is needed, with no topology or
measure on the space of bilateral series.

This module proves consequences of a supplied functional equation; it does not
assert analytic convergence or existence of a functional equation. No
polynomial is cancelled on the bilateral-series module.
