# Unequal-rank convergence and rationality over every nonarchimedean local field

Module `Langlands.Representation.RankinSelberg.LocalFieldUnequalRankAnalyticStatement`,
declaration `Langlands.RankinSelberg.LocalFieldUnequalRankAnalyticStatement : Prop`.

## Statement

The statement covers every nonarchimedean local field `F` of any characteristic, with Borel
measurable structures on `F`, `GL_(n+1)(F)`, its upper unipotent subgroup and the quotient
`LeftUnipotentQuotient n F`. It fixes ranks `n` and a block `j, k`, the residue cardinality `q`
of `F`, and an absolute value `abv` normalized by `abv ϖ = q⁻¹` for a uniformizer `ϖ` and
`abv x = 1` on valuation units. It also takes every unitary additive character `ψ`, every quotient
measure `μ` compatible with the Haar measures (with right-invariant unipotent Haar measure), every
additive Haar measure `ν`, every representation `π` of `GL_(n+(j+k+1)+1)(F)` of Whittaker type
for the standard character, every representation `σ` of `GL_(n+1)(F)` of Whittaker type for the
inverse standard character, and nonzero functionals `ℓ`, `ℓ'`. For all of these, the published
`UnequalRankAnalyticConclusion j k q ψ abv μ (rectangularMeasure ν j (n+1)) π σ ℓ ℓ'` holds:

1. for all model functions `f`, `f'` there is `a` such that the block integral converges
   absolutely (`UnequalRankConverges`) for every `s` with `a < Re s`;
2. every block model integral has a rational continuation in `q^(-s)`;
3. the block values have a common denominator;
4. they have a normalized generator.

The binders copy the accepted Task 5889 statement `LocalFieldUnequalRankFunctionalEquationStatement`.
The differences: the ranks are `(n j k)` in place of `(n r)` with `n < r`, `ν` need not be
self-dual, and `π` has rank `n + (j + k + 1) + 1`. The conclusion is the one used by the
published p-adic `UnequalRankAnalyticStatement`. That statement is for `PadicField` only, takes `q`
and `abv` from the field data, and uses Borel instances given by `borel`.

## Provenance

Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105
(1983), Theorem (2.7)(i)–(ii), printed page 390. The theorem is stated there for an arbitrary
nonarchimedean local field.
