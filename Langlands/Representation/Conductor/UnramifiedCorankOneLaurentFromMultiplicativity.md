# The Laurent clause from L- and gamma-factor multiplicativity

Author: Worker 8. All declarations are in `Langlands.Conductor`. The module
proves `UnramifiedCorankOneLaurentStatement`
([`UnramifiedCorankOneLaurentStatement`](UnramifiedCorankOneLaurentStatement.md))
from two general-field statements, neither of which is proved here:

```lean
theorem unramifiedCorankOneLaurent_of_multiplicativity
    (hL : LocalFieldPrincipalSeriesLFactorMultiplicativityStatement.{uF, uV})
    (hG : LocalFieldPrincipalSeriesGammaMultiplicativityStatement.{uF, uV}) :
    UnramifiedCorankOneLaurentStatement.{uF, uV}
```

- `Langlands.RankinSelberg.LocalFieldPrincipalSeriesLFactorMultiplicativityStatement`
  ([`LocalFieldPrincipalSeriesLFactorMultiplicativityStatement`](../RankinSelberg/LocalFieldPrincipalSeriesLFactorMultiplicativityStatement.md)),
  JPSS 1983, Theorem (3.1)(ii), for `π × I(z)` over every nonarchimedean local
  field: the L-polynomials `P_I` of `π × I(z)` and `P_i` of `π × χ_(z_i)` exist,
  and `X^e ∏_i P_i = Q₀ P_I` for some `Q₀ : ℂ[X]` and `e : ℕ`.
- `Langlands.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityStatement`
  ([`LocalFieldPrincipalSeriesGammaMultiplicativityStatement`](../RankinSelberg/LocalFieldPrincipalSeriesGammaMultiplicativityStatement.md)),
  JPSS 1983, Theorem (3.1)(i), in the same setting. The proof uses only the
  functional equation it contains for `π × I(z)`.

Both statements are proved in the Library
(`localFieldPrincipalSeriesLFactorMultiplicativity` and
`localFieldPrincipalSeriesGammaMultiplicativity`). The theorem
`unramifiedCorankOneLaurent`
([`SphericalCorankOneLaurentProof`](SphericalCorankOneLaurentProof.md))
applies `unramifiedCorankOneLaurent_of_multiplicativity` to these proofs.

Notation: `Ψ(s, W, W') = corankOneIntegral ψ abv μ W W' s`,
`X = spectralPoint q s` (`= q^(-s)`), and `χ_z` is the unramified character
`character h.uniformizer z` with `χ_z(ϖ) = z`.

## Auxiliary lemmas

**Laurent polynomials.** `exists_laurentEval_eq_zpow_mul`: for every Laurent
polynomial `b` there are `N : ℤ` and `Q : ℂ[X]` with `b(z) = z^N Q(z)` for
every `z : ℂˣ`. The proof clears the negative powers with Mathlib's
`LaurentPolynomial.exists_T_pow` and evaluates with the published
`laurentEval_toLaurent` and `laurentEval_T`.

**Unramified twists of the rank-one L-polynomial.**
`characterZetaValues_unramified`: if `χ(x) = |x|^u` for all `x`, and `e` is a
map of rational functions that turns a continuation of `f` into one of
`s ↦ f(s + u)`, then the rank-one zeta values of `π × χ` are the `e`-images of
those of `π × 1`. The proof unfolds `characterZetaValues` to the published
`unequalRankZetaValues` of the block `j = 0`, `k` and applies the published
`unequalRankZetaValues_unramified_right`, after writing `χ` as the twist of
the trivial character (`HighlyRamified.twist_rankOneCharacter_one`).

`isCharacterLPolynomial_unramified`: if `P` is the L-polynomial of `π × 1`
(`IsCharacterLPolynomial ... 1 π P`), then `P(zX)` is the L-polynomial of
`π × χ_z`, for every `z : ℂˣ`. The proof writes `z = q^(-u)` with the
published `HighlyRamified.exists_spectralShiftUnit_eq`, identifies `χ_z` with
`|·|^u` by `unramifiedCharacter_eq_abv_cpow`, and transports the normalized
generator `P` along the rescaling `X ↦ zX` (`IsNormalizedGenerator.rescale`
with `hasRationalContinuation_shift_iff`).

**The block `j = k = 0`.** With zero rectangular rows the unequal-rank
integral of the block `j = k = 0` is the corank-one integral.
`unequalRankConverges_rectangular_zero_iff` states this for convergence and
`unequalRankIntegral_rectangular_zero` for the integral; they use the published
`rectangularMeasure_zero_rows`,
`InducedTailIntermediate.unequalRankConverges_zero_rows_iff`,
`unequalRankIntegrand_zero_zero` and `unequalRankIntegral_zero_zero`.

## The proof of `unramifiedCorankOneLaurent_of_multiplicativity`

Fix the data of the Laurent statement: `π` on `GL_(n+2)(F)` generic with
nonzero `ℓ`, the L-polynomial `P` of `π × 1`, `x : Fin (n + 1) → ℂˣ`, a nonzero
`ℓ'` on `I(x)`, `W`, `W'` in the two models, and a half-plane where
`Ψ(s, W, W')` converges.

1. **Setting.** The Borel hypotheses identify each measurable structure of
   the statement with `borel` (`BorelSpace.measurable_eq`), as in the two
   general statements. `F` is Hausdorff and totally disconnected
   (`Langlands.BruhatTits.localField_t2Space`,
   `localField_totallyDisconnectedSpace`). A self-dual Haar measure `ν` for
   `ψ` comes from `Langlands.AllField.HarmonicAnalysis.padicSelfDualMeasureExists`
   applied to `LocalFieldData.ofInstances F`. `π` is of Whittaker type by
   `isOfWhittakerType_of_isGeneric_localField`.
2. **L-polynomials (part (ii)).** `hL` at `r = n + 1` gives `P_I`, the `P_i`,
   `Q₀` and `e`. Since `n ≤ n + 1`, the symmetric relation for `P_I` is the
   pair relation `IsPairLPolynomial` at every compatible quotient measure, in
   particular at `μ` (`h.measure`). By `isPairLPolynomial_of_lt` at the block
   `j = k = 0`, `P_I` is the normalized generator of the zeta values
   `unequalRankZetaValues ... 0 0 μ (rectangularMeasure ν 0 (n + 1)) π I(x)`.
3. **Rational continuation (part (i)).** `hG` gives a gamma factor of
   `π × I(x)`; unfolding the symmetric and pair relations at `n < n + 1` gives
   `IsUnequalRankGammaFactor`. Its functional equation at `μ`, `ℓ`, `ℓ'`, for
   the block `j = k = 0`, gives a rational function `R` with
   `HasRationalContinuation q` of the block integral of `(W, W')`.
4. **Membership.** The convergence hypothesis transfers to the block
   (`unequalRankConverges_rectangular_zero_iff`), so `R` is a zeta value of the
   block (`unequalRankModel_mem_zetaValues`). By the generator property
   (`clearsDenominators`, `mem_zetaSpan`), `P_I R` is a Laurent polynomial `b`.
5. **Rank-one factors.** For each `i`, the symmetric relation for `P_i` (rank
   `0 ≤ n + 1`) at the compatible measure `rankOneQuotientHaar F`
   (`rankOneQuotientHaar_isCompatible`) gives, through the published
   `IsPairLPolynomial.isCharacterLPolynomial`, that `P_i` is the L-polynomial of
   `π × χ_(x_i)`. By `isCharacterLPolynomial_unramified` so is `P(x_i X)`, and
   `IsNormalizedGenerator.unique` gives `P_i = P(x_i X)`.
6. **Conclusion.** Apply `exists_laurentEval_eq_zpow_mul` to
   `b · Q₀ · T^(-e)`, which gives `N` and `Q`. On the half-plane of the
   continuation of `R`, put `z = q^(-s)` (`spectralUnit`). There
   `Ψ(s, W, W') = R(z)` and `R(z) P_I(z) = b(z)`
   (`laurentEval_eq_of_laurentToRatFunc_eq`), and
   `∏_i P(x_i z) = ∏_i P_i(z) = z^(-e) Q₀(z) P_I(z)` from
   `X^e ∏_i P_i = Q₀ P_I`. Hence
   `Ψ(s, W, W') ∏_i P(x_i z) = b(z) Q₀(z) z^(-e) = z^N Q(z)`.

## Source

H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), 367-464, literature ID
`jpss-1983-rankin-selberg`, Theorem (3.1) (printed pages 404-405), with
Theorem (2.7) (printed pages 390-391) for the fractional ideal and its
generator. The derivation above is the standard one: the integral lies in the
ideal generated by `L(s, π × I(x))`, and by (3.1)(ii) this L-factor lies in
`∏_i L(s, π × χ_(x_i)) ℂ[q^(-s), q^s]`. The identification
`L(s, π × χ_z) = P(z q^(-s))⁻¹` is the unramified twist of JPSS's L-factor.
