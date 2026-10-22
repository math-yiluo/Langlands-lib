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
  paragraph notes that `L(s, π × σ)` does not depend on `ψ`; that is not
  proved in the Library.
- **Gamma factor (derived).** JPSS do not state a gamma convention at (2.12).
  The gamma factor is `γ = ε L(1 - s, π̃ × σ̃)/L(s, π × σ)` (Jacquet and
  Shalika 1985, (4.1), printed page 326). Since `L` and `ε` follow the
  convention and contragredients keep ranks, `γ` follows it too. The gamma
  relation here uses that convention.

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
  `ε(s, π × σ, ψ) = ε(s, σ × π, ψ)` are not proved in the Library, and nothing
  here depends on them.
- **Whittaker functionals.** For `r < n` the representation `π` is the test,
  so the relations use its `ψ̄`-Whittaker functionals. This is the JPSS
  convention in (2.12). For a generic `π` they are nonzero (conjugate by a
  diagonal matrix), but that is not proved in the Library. The nonvacuity
  parts of the gamma and epsilon relations require nonzero functionals of both
  representations.
- **Measures.** `IsPadicPairLPolynomial` quantifies over every compatible
  quotient measure and requires one to exist, like the published p-adic
  epsilon and gamma relations. So uniqueness needs no uniqueness of
  compatible measures, and a missing measure gives no witness. Compatible
  measures agree up to positive scalars (not proved in the Library). A
  positive scalar does not change the L-polynomial (published
  `isPairLPolynomial_smul_measure`).
- **Field.** `F` is a p-adic field, not an arbitrary nonarchimedean local
  field. The canonical topological data are published only for `PadicField`.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. There is no `sorry` and no new axiom.
