# Algebraic comparison for equal-rank gamma existence

Author: Worker 364.

This module supplies the algebraic comparison used by
`Langlands.RankinSelberg.equalRankGammaExistence` in the companion
`EqualRankGammaExistenceProof` module. Its four helper theorems live in
`Langlands.RankinSelberg.EqualRankGammaReduction`. Their hypotheses are
explicit; the companion proof supplies them from published analytic,
Fourier and trilinear-form theorems.

## Cross identities and normalization

`trilinear_cross_of_unique` takes two curried complex-linear trilinear
forms `B` and `Bd`. Assume `B ≠ 0` implies that `Bd` is a scalar multiple
of `B`. Their values then satisfy the cross identity

```text
Bd(i) B(j) = Bd(j) B(i).
```

The proof splits on `B = 0`. Both products vanish in that case; otherwise
substitution of the scalar multiple and commutativity prove the identity.
Thus an exceptional set for the zeros of a fixed form value is unnecessary.

`rational_cross_of_normalized_cross` assumes rational families `R i` and
`Rd i`, nonzero polynomials `P` and `Pd`, a finite exceptional spectral
set `E`, and families of scalar values `B s i` and `Bd s i`. At their
respective regular points these satisfy

```text
B s i  = P(q^(-s)) R_i(q^(-s))
Bd s i = Pd(q^(-(1-s))) Rd_i(q^(-(1-s))).
```

Assume the normalized values have the cross identity outside `E`.
Put `δ = q⁻¹`, represented by a complex unit. The proof enlarges `E` by
the roots of `P` and by the image of the roots of `Pd` under `z ↦ δ/z`.
If `q^(-s)` avoids this finite union, both polynomial evaluations are
nonzero: the reflected assertion uses `δ/q^(-(1-s)) = q^(-s)`.
The regular-point identities permit cancellation of their common product.
The published `RationalGammaComparison.rational_cross_of_spectral_cross`
then upgrades the resulting spectral equality to the identity

```text
subst δ (Rd i) * R j = subst δ (Rd j) * R i
```

of rational functions. That theorem supplies infinitely many regular
spectral points and applies rational-function uniqueness; no evaluation
at a pole is used here.

`exists_gamma_of_normalized_cross` additionally assumes a nonzero original
member `R i₀`, a unit `ζ` and an exponent `e`. It defines one rational
function using the published `gammaRatio`:

```text
G = subst δ (Rd i₀) / (C(ζ^e) * R i₀).
```

`gammaRatio_identity` and the cross identities show
`subst δ (Rd i) = C(ζ^e) * (G * R i)` for every index.
`gammaFunctionalEquation_of_rational_identity` yields the existing
`GammaFunctionalEquation` on its full three-denominator domain. The
helper proves existence of `G`; it does not assert `G ≠ 0` or require a
nonzero dual member.

## Actual coefficient models

`gammaEquation_of_continuedForms` works with the actual coefficient
models, quotient measure, scalar Fourier measure and dual model maps.
It takes original and inverse-transpose analytic conclusions, row Fourier
closure, a normalized original generator, a nonzero dual polynomial,
two trilinear families with separately guarded evaluation identities,
and their proportionality outside a finite spectral set.

Choice selects an actual row Fourier partner for each Schwartz–Bruhat
test and rational continuations for both integral families. The dual
analytic conclusion supplies the latter through `firstDualModelMap` and
`secondDualModelMap`; its integral is definitionally the existing
`dualEqualRankModelIntegral`. Triples of model vectors and row tests index
the rational families.

`IsNormalizedGenerator.exists_ne_zero` gives an original rational value
which is nonzero. Uniqueness of continuation, using `q > 1`, identifies
it with the chosen continuation for the same triple.
`exists_modelMinusOneScalar` supplies `ζ` for the second representation,
using its Whittaker-type hypothesis. It supplies the model scalar for
the specified functional as well. Applying the preceding algebra with
`e = n` gives one `G` before all test triples. The proof packages the
minus-one scalar, the nonzero original value, the actual Fourier
partners, both continuations and their functional equations into exactly
`EqualRankGammaEquation`.

## Provenance

These lemmas isolate the final algebra of JPSS §2.10, printed p.396,
using the published `RationalGammaComparison`, `ModelMinusOneScalar`
and `DualModels` modules. The original is H. Jacquet, I. I.
Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg Convolutions*,
American Journal of Mathematics 105 (1983), 367–464, registered source
`jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.391, 395 and 396 were read visually during this task.

The zero-form case split, finite reflected root set and quotient formula
are internal algebraic steps. The reflected dual parameter is consistently
`1-s`, following the derived reading explained in
`EqualRankContinuedFormsStatement` and its proof Markdown. The companion
final proof explains the relation to the source's displayed (2.10.3).
