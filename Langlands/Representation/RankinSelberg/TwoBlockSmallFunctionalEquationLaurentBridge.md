# Small functional-equation Laurent bridge

This module implements the passage from separately convergent original
and dual small-block spectral expansions to the required cleared coefficient
identity. The consumer theorem `smallFE_coefficient_identity` uses the published
`bilateralSpectralCoefficientUniqueness` proof, so it requires no scalar
uniqueness hypothesis. It retains the actual normalized generators, rational
continuations, normalized functional equation, weighted absolute convergence
and `HasSum` expansions. The earlier lemmas with an explicit
`BilateralSpectralCoefficientUniquenessStatement` input remain available.

It imports the published `BilateralSpectralEvaluation`,
`BilateralSpectralCoefficientUniquenessStatement`,
`BilateralSpectralCoefficientUniquenessProof`, and
`TwoBlockFirstBlockLaurentReflection` modules by their Lean names. The new
construction and bridge are authored by Worker 1191.

`normalizedGeneratorLaurentLift hP hRm` chooses the finite Laurent polynomial
clearing an actual rational value `R ∈ vals` by the supplied normalized
generator `P`. Its specification is exactly
`laurentToRatFunc L = P * R`. The choice uses
`IsNormalizedGenerator.clearsDenominators (mem_zetaSpan hRm)`. Injectivity of
the Laurent embedding proves that every finite Laurent polynomial with this
image equals the chosen lift; this construction therefore has no ambiguity
in its value. It specializes the pointwise lifting idea already used by
`Langlands.RankinSelberg.laurentLift` in `LaurentEvaluation`, which instead constructs a trilinear map
from a supplied family of clearing witnesses.

For an original bilateral coefficient function `a`, a polynomial `P`, and a
finite Laurent polynomial `L` satisfying
`laurentToRatFunc L = P * R`, `cleared_series_eq_of_spectral_uniqueness`
uses the maximum of the spectral expansion's right-half-plane bound and the
rational continuation's bound. On that half-plane the actual finite Laurent
action preserves absolute summability. Its `HasSum` value is
`P(q^(-s)) * I(s)`. Rational continuation identifies `I(s)` with evaluation
of `R`, including the actual nonvanishing denominator guard; the Laurent
evaluation bridge therefore identifies this product with evaluation of `L`.
The embedded finite coefficients of `L` also converge absolutely and sum
to that evaluation. Applying the explicit scalar uniqueness hypothesis gives
`P.toLaurent • a = ofLaurentPolynomial L`.

`normalizedGenerator_cleared_series` obtains `L` from the actual property
`IsNormalizedGenerator vals P` and actual membership `R ∈ vals`, using the
chosen lift just defined and the preceding spectral lemma.
It does not replace a normalized generator by an arbitrary denominator.

`cleared_series_eq` applies `cleared_series_eq_of_spectral_uniqueness` to
the published `bilateralSpectralCoefficientUniqueness` theorem. It therefore
gives the same coefficient equality from the supplied finite rational lift,
rational continuation and convergent spectral expansion, with no scalar
uniqueness hypothesis and no normalized-generator premise. The latter premise
is needed only to construct a lift when none is supplied.

`smallFE_coefficient_identity_of_spectral_uniqueness` applies that argument
separately to the original and dual series, each on its own right half-plane.
It then invokes the already implemented
`normalizedFE_coefficient_identity_of_cleared`. That theorem reflects the
finite cleared dual Laurent polynomial and uses the supplied normalized
functional equation to conclude

```text
Pdual(q⁻¹ X⁻¹) • (n ↦ q^n a'(-n))
  = (C(zeta^e c) * T(d) * P.toLaurent) • a.
```

The integer exponent and sign agree with
`spectralPoint q (1-s) = q⁻¹ * (spectralPoint q s)⁻¹`.
No overlap between the reflected and original convergence half-planes is
assumed, and no polynomial is cancelled on the bilateral module.

`smallFE_coefficient_identity` applies the preceding conditional theorem to
the published `bilateralSpectralCoefficientUniqueness` proof. Its remaining
arguments and conclusion are the same, including the separate existential
half-plane bounds and `HasSum` interfaces for both original coefficient
functions. The named `reflectSeries q a'` in the Lean conclusion is exactly
`n ↦ (q : ℂ)^n * a'(-n)`, with integer powers.

This is internal proof packaging derived from the named imported definitions,
finite-action evaluation theorems, and the published scalar uniqueness proof.
It adds no source theorem or representation-theoretic
assumption. It does not prove determinant-slice convergence, the upper or lower
geometric comparison, measure disintegration, or the full first-block target.
