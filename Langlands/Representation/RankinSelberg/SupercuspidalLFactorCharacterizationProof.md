# Henniart 2002, Théorème 1.6(b)

This module, in namespace `Langlands.RankinSelberg`, proves the Library
statement `SupercuspidalLFactorCharacterizationStatement` (module
`PairLFactorCharacterizationStatement`): the characterization of supercuspidal
representations by L-factors of pairs (Henniart, *Une caractérisation de la
correspondance de Langlands locale pour GL(n)*, Bull. SMF 130 (2002),
Théorème 1.6(b), (i) ⇔ (ii), printed pages 590-591). An irreducible admissible
representation `π` of `GL_(n+2)(F)` is supercuspidal if and only if
`L(s, π × ρ) = 1` for every irreducible supercuspidal representation `ρ` of
`GL_(r+1)(F)` with `r ≤ n`.

The proof has no new mathematics: it supplies the five hypotheses of the
conditional theorem
`SupercuspidalLFactorCharacterization.supercuspidalLFactorCharacterization_of`
(module `SupercuspidalLFactorCharacterizationReduction`, with its helper module
`SupercuspidalLFactorCharacterizationSupport`; see their Markdown files for the
mathematical argument) with published Library theorems.

## `temperedTwistSupercuspidalPole`

`temperedTwistSupercuspidalPole : TemperedTwistSupercuspidalPoleStatement.{uF, uV, uW}`:
for an irreducible tempered representation `τ` of `GL_k(F)` and a real `u`,
some irreducible supercuspidal `ρ` of rank at most `k`, and smaller than `k`
unless `τ` is supercuspidal, makes `L(s, ν^u τ × ρ)` have a pole at `s = 0`.
It is the published conditional theorem `temperedTwistSupercuspidalPoleReduction`
applied to

- tempered block exhaustion, `Classification.temperedBlockExhaustion F T`, used
  with the canonical topological data `F.canonicalTopologicalData` of the
  `p`-adic field `F`;
- JPSS 1983 (8.2), the L-factor of square-integrable pairs,
  `squareIntegrableLFactor`;
- JPSS 1983 (8.4), the L-factor of tempered pairs, `temperedLFactor`.

## `supercuspidalLFactorCharacterization`

`supercuspidalLFactorCharacterization : SupercuspidalLFactorCharacterizationStatement.{uF, uV, uW}`
is `supercuspidalLFactorCharacterization_of` applied to

- `h81 := supercuspidalUnequalRankLFactor` (JPSS 1983, (8.1)(i));
- `h94 := langlandsTypeLFactor` (JPSS 1983, (9.4)(3));
- `hS1V`, `hS1W := Classification.supercuspidalTemperedQuotientSingleBlock`
  (a tempered Langlands datum with supercuspidal Langlands quotient has one
  block), at universes `uV` and `uW`;
- `hS2 := temperedTwistSupercuspidalPole` above.

Lean infers the universe instances of each input from the hypotheses of
`supercuspidalLFactorCharacterization_of`. The theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

The support and reduction modules were written by Worker 1719; this module and
the assembly are by Worker 4855.
