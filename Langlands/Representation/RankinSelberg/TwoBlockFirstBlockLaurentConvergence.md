# Spectral series of the original and transformed small integrals

Author: Worker 1037.

This module supplies the analytic inputs of the small functional-equation step in
JPSS (1983), Section 4.9. It is derived internal packaging of published results.
The published `unequalRankAnalytic F T n j k` is JPSS Theorem 2.7(i)–(ii). It
assumes:

- full standard Whittaker type of the large representation;
- inverse-character Whittaker type of the small one;
- nonzero functionals.

Under these hypotheses every pair of coefficient-image vectors has an absolutely
convergent integral on a right half-plane.

## Fixed-rank wrappers

`unequalRankSliceCoefficientAt` and `unequalRankIntegrandAt` are the slice coefficient
and the integrand at a large rank `r` fixed by an equality `r = n + (j + k + 1)`.
The equality transports only types.

## Series

`smallIntegral_series` combines `unequalRankAnalytic` with the slice expansion of
`TwoBlockFirstBlockLaurentSlices`. On a right half-plane the actual fixed-rank small
integral of coefficient-image vectors is the absolutely summable series of its slice
coefficients. This is exactly the summability and `HasSum` interface of the
published `smallFE_coefficient_identity`.

`dualSmallIntegral_series` proves the same statement for the published transformed
integral `dualUnequalRankModelIntegralAt`. It is the integral of the
inverse-transpose pair, taken for the inverse additive character and the exchanged
blocks. The actual model vectors come from the published equivalences
`translatedFirstDualModelEquiv` and `secondDualModelMap`. Their Whittaker types and
nonvanishing come from `DualWhittakerType` and `DualModels`.

## Slice integrability

`smallIntegrand_integrableOn_slice` and `dualIntegrand_integrableOn_slice` prove
integrability on every determinant slice of the inner integral at `s = 0`. The proof
uses one convergent parameter and the constant slice factor `(q^(-s))^m`.
