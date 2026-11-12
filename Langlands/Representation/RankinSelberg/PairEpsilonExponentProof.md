# The exponent of the epsilon factor of a pair from the change of additive character

Author: Worker 4803. Module `Langlands.Representation.RankinSelberg.PairEpsilonExponentProof`,
namespace `Langlands.RankinSelberg`. Universes: `uF` (p-adic fields), `uV` and `uW`
(carriers of the two representations), independent.

## Statement: `PairEpsilonExponentReductionStatement.{uF, uV, uW}`

The implication below, proved as `pairEpsilonExponentReduction`:

`EqualRankEpsilonCharacterChangeStatement.{uF, uV, uW} →
PairEpsilonExponentStatement.{uF, uV, uW}`.

The module first proves the theorem `pairEpsilonExponent_of_characterChange`, which
also takes `UnequalRankEpsilonCharacterChangeStatement.{uF, uV, uW}` as a hypothesis.
`pairEpsilonExponentReduction` supplies that hypothesis by the published Library
theorem `pairFactorCharacterChange.2` (module `PairFactorCharacterChangeProof`).

The conclusion is the published statement of Bushnell, Henniart and Kutzko (1998),
introduction, printed p. 703. Let `π` and `σ` be irreducible admissible
representations of `GL_(r+1)(F)` and `GL_(t+1)(F)`. Then there is an integer `a`
such that for every nontrivial additive character `ψ`, every Haar measure `ν`
self-dual for `ψ` and every epsilon factor `ε(s, π × σ, ψ) = c q^(-ms)` of the pair
(`IsPadicSymmetricEpsilonFactor F ψ ν π σ (c, m)`),
`m = a + (r+1)(t+1) n(ψ)`. Here `n(ψ)` is `additiveConductor ψ`, the largest `k`
with `ψ` trivial on `p^(-k)`.

The two change-of-character laws are published Library statements. Write
`ψ^b(x) = ψ(bx)` for `b ∈ Fˣ` (`ψ.scale b`).

- `UnequalRankEpsilonCharacterChangeStatement` (Cogdell and Piatetski-Shapiro
  1994, Lemma 2.1 and its proof, printed pp. 161–163): for `r ≠ t`, central
  characters `ω_π`, `ω_σ`, measures `ν` self-dual for `ψ` and `ν'` self-dual for
  `ψ^b`, and an epsilon factor `(c, m)` for `ψ` and `ν`, the pair has an epsilon
  factor `(c', m')` for `ψ^b` and `ν'` with `m' = m + (r+1)(t+1) ord b` and an
  explicit `c'`. It is proved in the Library: `pairFactorCharacterChange` proves
  `PairFactorCharacterChangeStatement`, whose second component is this statement.
- `EqualRankEpsilonCharacterChangeStatement` (internal derived statement of the
  Library; compare Jacquet 2009, Remark 2.2, at an Archimedean place): the same
  for `r = t`, with `m' = m + (r+1)² ord b`. It remains the hypothesis of the
  statement; the module does not assert it.

## Provenance

Internal. Bushnell, Henniart and Kutzko (1998), introduction, printed p. 703, write
"In fact, f(π1 × π2, ψ) = n1n2c(ψ) + f(π1 × π2), where f(π1 × π2) is independent
of ψ", with no proof. The Lean proof derives this from the change of additive
character: it uses the two published change-of-character statements above (the
unequal-rank one through its published proof) and published lemmas of the Library.

## Proof

`pairEpsilonExponent_of_characterChange`. Fix `π` and `σ`.

1. Both representations have central characters `ω_π`, `ω_σ` by the published
   Schur lemma `UniformRankOneTwist.exists_hasGLCentralCharacter`.
2. The exponent part of the two hypotheses gives, for either rank order: if
   `(c, m)` is an epsilon factor for `ψ` and `ν`, and `ν'` is self-dual for `ψ^b`,
   then some `(c', m')` is an epsilon factor for `ψ^b` and `ν'` with
   `m' = m + (r+1)(t+1) ord b`. The case `r = t` uses the equal-rank hypothesis
   after identifying `t` with `r`; the case `r ≠ t` uses the unequal-rank one.
3. If the pair has no epsilon factor for any `ψ` and any self-dual `ν`, every
   integer `a` works, and the proof takes `a = 0`.
4. Otherwise fix an epsilon factor `(c₀, m₀)` for some `ψ₀` and `ν₀`, and put
   `a = m₀ - (r+1)(t+1) n(ψ₀)`. Let `(c, m)` be an epsilon factor for `ψ` and `ν`.
   By the published `exists_unit_scale_eq`, `ψ = ψ₀^b` for some `b ∈ Fˣ`. Step 2,
   with `ν' = ν`, gives an epsilon factor `(c', m')` for `ψ` and `ν` with
   `m' = m₀ + (r+1)(t+1) ord b`. The epsilon factor is unique
   (`IsPadicSymmetricEpsilonFactor.unique`), so `m = m'`. The published
   `additiveConductor_scale` gives `n(ψ₀^b) = n(ψ₀) + ord b`. Hence
   `m = a + (r+1)(t+1) n(ψ)`.

`pairEpsilonExponentReduction` is `pairEpsilonExponent_of_characterChange` applied to
`pairFactorCharacterChange.2`.
