# Compact torus criterion for the actual Whittaker quotient

This internal supporting construction specializes the compact-torus criterion of
`LeftCosetSpace.CompactTorusQuotientIntegral` to the actual adelic general linear
group and its actual upper unitriangular subgroup. It works over a number field
`F` in any universe, with arbitrary matrix size `n`. Its finiteness theorem
assumes compactness of the additive adelic quotient, as used in the diagonal
Haar-modulus computation. The torus measure can be any Haar normalization.

## Diagonal coordinates and modulus

`diagonalHom` sends a tuple of ideles to its actual diagonal adelic point.
`diagonalTorus` is its image subgroup. Injectivity follows by evaluating the
diagonal matrix entries. `diagonalEquiv` identifies this subgroup with the full
idele torus. Its inverse has diagonal entries as values and inverse-matrix
diagonal entries as inverse values; these formulas prove continuity of the
inverse in the units topology. They give the continuous multiplicative
isomorphism `diagonalContinuousEquiv`.

`torusMeasure` pushes an arbitrary torus Haar measure through this isomorphism;
`torusMeasure_isHaar` records that the transported measure is Haar.
`torusModulus` transports `AdelicDiagonalUnipotentModulus.diagonalModulus`, the
product of the idelic norms of `d_i/d_j` for `i < j`, to `diagonalTorus`.
`diagonalTorus_normalizes` proves normalization of the actual unipotent subgroup.
`isConjModulus_torus` uses the existing arbitrary-diagonal Haar-character theorem
and the identity `c * map(alpha, nu) = nu` in measure-scaling notation to obtain
`map(alpha, nu) = c^(-1) * nu`. Thus the integration weight is the inverse
positive-root modulus, in the precise convention of `IsConjModulus`.

## Actual factorization and rational subgroup

`standardCompactPoints` transports the standard compact adelic matrix subgroup
to the actual group-scheme point carrier. Its compactness follows from the
multiplicative homeomorphism between these carriers.
`exists_diagonal_unipotent_compact` gives `g = a * v * k` with `a` in the actual
diagonal subgroup, `v` upper unitriangular, and `k` in this compact subgroup.
The proof applies the published adelic Iwasawa factorization `g = b * k`, takes
the diagonal units of `b`, and observes that `b * diag(d)^(-1)` is unitriangular.
Conjugation by the inverse diagonal element reorders these factors to the
required diagonal-unipotent order.

`unipotentRationalImage_le_unipotent` and `unipotentRationalImage_comap` identify
the principal rational-unipotent subgroup in the ambient group and its pullback
to the actual adelic unipotent group. The pullback is exactly the rational
subgroup used by `Unfolding.unipotentFundamentalDomain`.

## Quotient finiteness theorem and proof

`lintegral_whittakerQuotient_eq` applies the two pushforwards in the definition of
`whittakerQuotientMeasure`. For a measurable nonnegative extended-real function
`f` invariant under left adelic-unipotent multiplication, its evaluation at
quotient representatives is its measurable descent. Its lower integral equals
the integral of `f` against ambient Haar restricted to the chosen fundamental
domain of the rational-unipotent subgroup. This identity needs no finiteness
assumption on `f` and no compact-additive-quotient assumption.

The theorem
`lintegral_whittakerQuotient_lt_top_of_compactTorusBound` assumes that, for every
compact ambient set `C`, there is a finite extended-real constant `B` such that,
for every `c` in `C`,

`integral_d diagonalModulus(d)^(-1) * f(gaugeDiagonalPoint(d) * c) <= B`.

It proves finiteness of the lower integral of `f(q.out)` for the defined
Whittaker quotient measure. Here `f` must be measurable and left invariant under
the actual adelic unipotent subgroup, and the integral over `d` uses the supplied
torus Haar measure.

The proof transports the assumed bounds to `HasCompactTorusBound` using the
measurable equivalence of torus coordinates. The principal unipotent subgroup
is countable, and its chosen fundamental domain has finite Haar mass by the
published compactness of the rational-unipotent quotient and its mass-normalizer
identity. The actual factorization, modulus and covolume results then supply all
hypotheses of the published fundamental-domain compact-torus criterion. The
two-pushforward identity transfers the resulting finiteness to the actual
Whittaker quotient. There is no right-compact invariance hypothesis on `f`.

## Provenance and scope

The definitions and lemmas are internal transports and specializations of
published infrastructure: adelic Iwasawa decomposition, triangular matrix
identities, the arbitrary-diagonal unipotent Haar character, the rational
unipotent fundamental domain, and the generic compact-torus criterion. No
external source claim is introduced. The compact-uniform torus estimate is an
explicit hypothesis of this supporting theorem; proving it for the weighted
Whittaker-Schwartz kernel and deriving the uniform half-plane remain separate
analytic obligations of `WhittakerSchwartzGaugeStatement`.
