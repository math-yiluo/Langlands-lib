# Change of additive character for generic pair gamma factors

Author: Worker 389.

This module proves how the JPSS pair gamma factor of two generic representations changes when
the additive character `ψ` is replaced by `ψ^b = ψ(b ·)`, `b ∈ Fˣ`. It is a supporting module
for the stable pair gamma comparison under highly ramified twists: the representation-side
stability theorem of Jacquet and Shalika in the Library assumes an additive character of
conductor exponent `0`, and this module is used to pass from an arbitrary `ψ` to such a
character. It introduces one definition, `gammaCharacterChangeMonomial`, and no axiom.

## Declarations

All declarations are in the namespace `Langlands.RankinSelberg`.

- `IsPairLPolynomial.unique_of_measure`: for fixed `q`, `ψ`, absolute value, quotient measure
  `μ`, `π` (rank `r + 1`) and `σ` (rank `n + 1`), pair L-polynomial certificates for two
  additive Haar measures `ν`, `ν'` are equal.
- `IsPadicPairLPolynomial.unique_of_measure` and `IsPadicSymmetricLPolynomial.unique_of_measure`:
  the same statement for the p-adic pair relation (canonical topology and Borel structures)
  and for the symmetric relation (larger rank first).
- `exists_isPadicSymmetricEpsilonFactor_characterChange`: for irreducible admissible `π`, `σ`
  of ranks `r + 1`, `t + 1` with central characters `ω_π`, `ω_σ`, a self-dual measure `ν` for
  `ψ`, `a ∈ Fˣ`, a self-dual measure `ν'` for `ψ^a` and an epsilon certificate `(c, m)` for
  `(π, σ, ψ, ν)` in the symmetric relation, there is an epsilon certificate `(c', m')` for
  `(π, σ, ψ^a, ν')` with `m' = m + N ord(a)` and
  `c' = c · ω_π(a)^(t+1) · ω_σ(a)^(r+1) · |a|^(-N/2)`, where `N = (r+1)(t+1)`.
- `gammaCharacterChangeMonomial F r t ω_π ω_σ b`: the rational function
  `ω_π(b)^(t+1) · ω_σ(b)^(r+1) · |b|^(-N/2) · X^(N ord b)`, `N = (r+1)(t+1)`, where `|·|` is the
  normalized absolute value and `ord` the normalized valuation of the canonical topological
  data. With `X = q^(-s)` it is the factor `ω_π(b)^(t+1) ω_σ(b)^(r+1) |b|^(N(s - 1/2))` of the
  classical formula.
- `genericGamma_characterChange`: for `ψ`-generic `π`, `σ` of ranks `r + 1`, `t + 1` with
  central characters `ω_π`, `ω_σ`, a self-dual measure `ν₀` for `ψ`, `b ∈ Fˣ`, a self-dual
  measure `ν` for `ψ^b`, and symmetric gamma certificates `G₀` for `(π, σ, ψ, ν₀)` and `G` for
  `(π, σ, ψ^b, ν)`, one has `G = gammaCharacterChangeMonomial F r t ω_π ω_σ b · G₀`.

## Implemented proofs

**Measure independence of L-polynomials.** In the unequal-rank case the L-polynomial
relation is quantified over all block splittings `r = n + (j + k + 1)`; the proof takes the
block `j = 0`, where the rectangular measure is the unit point mass on the empty rectangle
whatever the additive measure (`rectangularMeasure_zero_rows`). The two certificates are then
normalized generators of the same ideal and agree (`IsNormalizedGenerator.unique` through the
block relation's `unique`). In the equal-rank case the relation does not involve `ν`
(`isPairLPolynomial_self`). The p-adic forms install the canonical topology and Borel
structures and specialize the quantified quotient measure to one compatible measure supplied
by the first certificate. The symmetric form splits on the rank order.

**Epsilon change.** This splits on `r = t` and applies the published
`equalRankEpsilonCharacterChange` (equal ranks) or `pairFactorCharacterChange` (second
component, unequal ranks).

**Gamma change.** The proof:

1. transports genericity from `ψ` to `ψ^b` (`isGeneric_iff_character`);
2. takes the generic epsilon datum `e₀`, L-polynomial `P₀` and dual L-polynomial `D₀` at
   `(ψ, ν₀)` (`genericSymmetricEpsilonData_isPadic`, `genericSymmetricLPolynomial_isPadic`,
   `genericSymmetricDualLPolynomial_isPadic`), and rewrites `G₀` as
   `rationalGammaExpression δ e₀.1 e₀.2 P₀ D₀` by `symmetricGammaExpression`;
3. obtains the changed epsilon datum `e₁` at `(ψ^b, ν)` from the epsilon change above;
4. shows that `P₀` is also an L-polynomial at `(ψ^b, ν)`: the published
   `isPadicSymmetricLPolynomial_characterChange` gives it for `(ψ^b, ν₀)`, and measure
   independence identifies it with the generic L-polynomial at `(ψ^b, ν)`. The dual
   polynomial `D₀` is treated the same way for the inverse-transpose pair and the character
   `(ψ^b)^(-1) = (ψ^(-1))^b` (`UnitaryAdditiveCharacter.scale_scale`);
5. rewrites `G` as `rationalGammaExpression δ e₁.1 e₁.2 P₀ D₀` by `symmetricGammaExpression`
   and compares the two expressions: they share the L-polynomial quotient, and the epsilon
   monomials differ by the constant and the power of `X` above.

## Sources and provenance

This is an internal derivation from published Library results, not a numbered theorem of a
source. The classical formula `γ(s, π × σ, ψ^b) = ω_π(b)^(t+1) ω_σ(b)^(r+1) |b|^(N(s-1/2))
γ(s, π × σ, ψ)` follows from the corresponding epsilon formula of Jacquet, Piatetski-Shapiro
and Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983)
(`jpss-1983-rankin-selberg`), since the L-factors do not depend on `ψ`; in the Library the
epsilon formula is `pairFactorCharacterChange` and `equalRankEpsilonCharacterChange`. The
self-dual measures are those of `LocalFactor.PadicAbelian.SelfDualHaar`.
