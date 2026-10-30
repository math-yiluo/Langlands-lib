# Pair factors of actual p-adic representations

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`,
collects the forms of the local factors of pairs used by statements about
actual representations of `GL_m(F)` over a p-adic field `F` with its canonical
topological data. It defines one relation for the L-polynomial of a pair and
three relations for the gamma, epsilon and L factors of a pair of either rank
order. It also proves uniqueness and invariance under representation
equivalences for these relations and for the published p-adic epsilon
relation. The module states no theorem target. Every lemma in it is proved.

## Source

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*, Amer.
J. Math. 105 (1983).

- **Theorem 2.7, printed pages 390-391.** For `π` on `G_r = GL_r(F)` and `σ`
  on `G_t`, `t ≤ r`, the zeta integrals span a fractional ideal of
  `ℂ[q^{-s}, q^{s}]` with a unique generator `L(s, π × σ) = 1/P(q^{-s})`,
  `P(0) = 1`, independent of the block `j` when `t < r`. Then
  `ε(s, π × σ, ψ)` is defined by the functional equations (1) and (2). The
  published `IsPairLPolynomial`, `IsPairEpsilonFactor` and
  `IsPairGammaFactor` state these with the candidate `π` first.
- **(2.12), printed page 403.** In the integrals of Theorem 2.7, `W` lies in
  the `ψ`-Whittaker model of `π`, the representation of larger or equal rank,
  and `W'` in the `ψ̄`-Whittaker model of `σ`. For `r = t`, exchanging the
  roles of `ψ` and `ψ̄` gives `L(s, π × σ) = L(s, σ × π)`. "If `r > t`, we
  write by convention `L(s, σ × π) = L(s, π × σ)`." It is "easy to see
  directly" that `ε(s, π × σ, ψ) = ε(s, σ × π, ψ)` for `r = t`, "thus, if
  `r > t`, we may also define `ε(s, σ × π, ψ) = ε(s, π × σ, ψ)`." The same
  paragraph notes that `L(s, π × σ)` does not depend on `ψ`. The Library
  proves the case of scaling by a unit for the ordered relation:
  `isPairLPolynomial_characterChange_canonical`
  (`RankinSelberg/CanonicalPairLFactor`) shows that the published
  `IsPairLPolynomial`, for any supplied topological data of `F`, the quotient
  measure `unipotentQuotientHaar` and a fixed additive Haar measure, holds for
  `ψ` if and only if it holds for `ψ.scale a`, `a ∈ F^×`, with the same
  polynomial. This module states no `ψ`-independence for its own relations,
  and nothing here depends on it.
- **Gamma factor (derived).** JPSS do not state a gamma convention at (2.12).
  The gamma factor is `γ = ε L(1 - s, π̃ × σ̃)/L(s, π × σ)` (Jacquet and
  Shalika 1985, (4.1), printed page 326). Since `L` and `ε` follow the
  convention and contragredients keep ranks, `γ` follows it too. The gamma
  relation here uses that convention.

The companion quotient-measure construction cited below specializes Folland,
*A Course in Abstract Harmonic Analysis*, second edition (2015), §2.6,
Proposition 2.50 and Theorem 2.51, printed pages 62–63, formula (2.52).
`UnipotentQuotient.md` explains the Library's left-coset/right-action convention
and its fixed Haar normalizations.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data. In each
relation `q` is the residue cardinality and the absolute value is the
normalized one. `ψ` is a `UnitaryAdditiveCharacter` of `F` and `ν` an additive
Haar measure on `F`. `π` is an actual representation of `GL_{r+1}(F)` on a
complex vector space in universe `uV`, and `σ` one of `GL_{n+1}(F)` in universe
`uW`.

`IsPadicPairLPolynomial F ψ ν π σ P`:

- (a) a compatible quotient measure on `N_{n+1} \ GL_{n+1}(F)` exists, with
  right invariance of the unipotent Haar measure;
- (b) for every compatible quotient measure `μ`, `P` satisfies the published
  `IsPairLPolynomial q ψ abv μ ν π σ P`.

Part (b) says that `P` is the normalized generator (`P(0) = 1`) of the JPSS
zeta values of the pair. When `n < r` this holds in every block, and when
`n = r` it is the equal-rank condition. When `n > r` the relation is false. So
`L(s, π × σ) = 1/P(q^{-s})`. Part (a) makes (b) nonvacuous.

`IsPadicSymmetricGammaFactor F ψ ν π σ G` is
`IsPadicPairGammaFactor F ψ ν π σ G` when `n ≤ r` and
`IsPadicPairGammaFactor F ψ ν σ π G` when `r < n`. In both cases the
representation of larger rank is the candidate, with its `ψ`-Whittaker
functionals, and the other is the test, with its `ψ̄`-Whittaker functionals.
In equal rank `π` is the candidate. `IsPadicSymmetricEpsilonFactor` (witness
`e = (c, m)` for `ε(s) = c q^{-ms}`, over the published
`IsPadicPairEpsilonFactor`) and `IsPadicSymmetricLPolynomial` (over
`IsPadicPairLPolynomial`) are defined the same way.

## Proved lemmas

- `IsPadicPairEpsilonFactor.unique` and `IsPadicPairEpsilonFactor.congr_equiv`
  are the p-adic forms of the published `IsPairEpsilonFactor.unique` (using
  `q > 1`) and `IsPairEpsilonFactor.congr_equiv`.
- `IsPadicPairLPolynomial.unique`: take a measure from (a) and apply the
  published `IsPairLPolynomial.unique`.
- `IsPadicPairLPolynomial.congr_equiv` transfers the relation along
  equivalences of both representations. It uses the published
  `isPairLPolynomial_congr_equiv` for each measure.
- For each symmetric relation: `_of_le` and `_of_lt` unfold it in the two
  rank orders, and `.unique` and `.congr_equiv` follow from the corresponding
  pair lemmas. All equivalences may change carrier universes (`uV₂`, `uW₂`).

## Interpretation

- **Convention.** JPSS (2.12) define the factors of `σ × π`, with `σ` of
  smaller rank, as those of `π × σ`. The symmetric relations implement exactly
  this definition. In equal rank they keep the given order. JPSS's equal-rank
  identities `L(s, π × σ) = L(s, σ × π)` and
  `ε(s, π × σ, ψ) = ε(s, σ × π, ψ)` are proved downstream as exchanges of
  certificates, in `RankinSelberg/EqualRankFactorSwapProof`.
  `isPadicPairLPolynomial_swap_equalRank` proves
  `IsPadicPairLPolynomial F ψ ν π σ P ↔ IsPadicPairLPolynomial F ψ ν σ π P`
  for equal ranks, at the same `ψ` and the same supplied additive Haar
  measure `ν`, for arbitrary representations. `equalRankFactorSwap` proves
  `EqualRankFactorSwapStatement`: the same exchange of the L, epsilon and
  gamma certificates, at the same `ψ` and a self-dual
  `ν : SelfDualHaar F.canonicalTopologicalData ψ`, for `π` and `σ` of
  Whittaker type for `standardCharacter ψ n`, with independent carrier
  universes `uV` and `uW`. These results transport a given certificate; they
  do not assert that any factor exists. Nothing here depends on them, and the
  symmetric relations remain defined with the given order in equal rank.
- **Whittaker functionals.** For `r < n` the representation `π` is the test,
  so the relations use its `ψ̄`-Whittaker functionals. This is the JPSS
  convention in (2.12). `Whittaker.characterChangeFunctionalEquiv` at
  `a = -1`, together with `standardCharacter_scale_neg_one`, gives a linear
  equivalence from the `ψ`-functional space to the inverse-character space
  (JPSS §2.1, printed page 385). It transports nonzero functionals, so a
  generic `π` has nonzero `ψ̄`-functionals. The nonvacuity parts of the gamma
  and epsilon relations require nonzero functionals of both representations;
  this transport does not prove analytic factor existence or the functional
  equation.
- **Measures.** `IsPadicPairLPolynomial` quantifies over every compatible
  quotient measure and requires one to exist, like the published p-adic
  epsilon and gamma relations. So uniqueness needs no uniqueness of
  compatible measures, and a missing measure gives no witness. With the
  `generalLinearHaar` and `unipotentHaar` normalizations fixed,
  `unipotentQuotientHaar_unique` in `RankinSelberg/UnipotentQuotient` proves
  that every compatible measure is exactly `unipotentQuotientHaar`.
  Existence is proved there by `unipotent_compatibleMeasureExists` and, for
  the p-adic statement, by `quotientHaarExistence` in
  `RankinSelberg/QuotientHaarExistence`. The L-polynomial uniqueness proof
  here uses only one compatible measure and does not depend on this stronger
  measure uniqueness theorem. Separately, a positive scalar does not change
  the L-polynomial (published `isPairLPolynomial_smul_measure`).
- **Field.** `F` is a p-adic field, not an arbitrary nonarchimedean local
  field. The canonical topological data are published only for `PadicField`.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. There is no `sorry` and no new axiom.
