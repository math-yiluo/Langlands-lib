# L-polynomials of pairs over general nonarchimedean local fields

Worker 8 adapts the published p-adic L-polynomial interface
(`IsPadicPairLPolynomial`, `IsPadicSymmetricLPolynomial` in
`RankinSelberg/PadicPairFactors.lean`) to a general nonarchimedean local field,
in the same way as `RankinSelberg/GeneralPairGamma.lean` adapts the gamma
relations. All declarations are in `Langlands.RankinSelberg`. This is a derived
definition unit. It proves no existence of L-polynomials and selects none.

## Setting and definitions

The field `F` has `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances. There is no characteristic restriction.
The two representations have positive ranks `r + 1` and `n + 1`, on arbitrary
complex modules in independent universes. The definitions impose no
admissibility, irreducibility or Whittaker-type condition.

`IsGeneralPairLPolynomial q ψ abv ν π σ P` installs the Borel measurable
structures of `F`, `GL_(n+1)(F)`, its upper unipotent subgroup and the
left-unipotent quotient, exactly as `IsGeneralPairGammaFactor` does. It then
asserts two things:

1. a compatible quotient measure exists: the Haar measure `unipotentHaar F n`
   is right invariant and `CompatibleMeasureExists` holds for
   `generalLinearHaar F n` and `unipotentHaar F n`;
2. for every compatible quotient measure `μ` on the left-unipotent quotient,
   `IsPairLPolynomial q ψ abv μ ν π σ P` holds.

`IsPairLPolynomial` (module `RankinSelberg/PairLFactor`) is the published JPSS
L-polynomial of a pair: for `n < r` the common normalized generator of the
zeta values of every block `r = n + (j + k + 1)`, for `r = n` the equal-rank
L-polynomial, and false for `r < n`. So `P` is the polynomial with
`L(s, π × σ) = 1 / P(q^(-s))` and `P(0) = 1`.

The integer `q`, the absolute value `abv` and the additive Haar measure `ν` stay
explicit, as in `IsGeneralPairGammaFactor`. The relation does not assert that
`q` is the residue cardinality, that `abv` is normalized, or that `ν` is self-dual.
A consumer that reads it as the local L-factor supplies those hypotheses in its
own statement.

`IsGeneralSymmetricLPolynomial q ψ abv ν π σ P` is the pair relation for
`(π, σ)` when `n ≤ r`, and for `(σ, π)` when `r < n`. The larger rank comes
first, and equal ranks keep the given order.

## Sources and derived provenance

Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions*,
American Journal of Mathematics 105 (1983), Theorem (2.7), printed pages
390–391, define `L(s, π × σ)` as the normalized generator of the ideal of the
zeta integrals. §2.12, printed page 403, defines the factors of a pair with the
smaller rank first by reversing the pair. Source `jpss-1983-rankin-selberg`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The quantification over compatible quotient measures and the rank-order
conditional copy the published p-adic definitions `IsPadicPairLPolynomial` and
`IsPadicSymmetricLPolynomial` word for word. Only the binders change: the
canonical topological data of a `PadicField` becomes an arbitrary local field,
and its residue cardinality and normalized absolute value become the explicit
`q` and `abv`. No published declaration is changed.

## Implemented proofs

`IsGeneralPairLPolynomial.unique` installs the Borel structures, takes the
compatible measure `μ` supplied by the first hypothesis, and applies the
published `IsPairLPolynomial.unique` at `μ`.
`IsGeneralPairLPolynomial.congr_equiv` keeps the existence clause and transports
the clause at each `μ` by the published `isPairLPolynomial_congr_equiv`. Both
representations can change carrier universes.

`isGeneralSymmetricLPolynomial_of_le` and `isGeneralSymmetricLPolynomial_of_lt`
unfold the conditional. `IsGeneralSymmetricLPolynomial.unique` splits it and
applies pair uniqueness in the selected order.
`IsGeneralSymmetricLPolynomial.congr_equiv` also splits it, and uses the two
equivalences in reverse order in the swapped branch.

`isGeneralPairLPolynomial_padic` sets the topology, valuation and local-field
instances to the canonical data of a `PadicField`, with its residue cardinality
and normalized absolute value. The general relation is then the published
`IsPadicPairLPolynomial` by definitional equality, proved by `Iff.rfl`.
`isGeneralSymmetricLPolynomial_padic` does the same for both rank branches,
also by `Iff.rfl`.
