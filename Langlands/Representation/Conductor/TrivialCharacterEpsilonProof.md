# Existence of the JPSS epsilon factor against the trivial character of `GL_1`

Module `Langlands.Representation.Conductor.TrivialCharacterEpsilonProof`. Author:
Worker 5550.

`Langlands.Conductor.trivialCharacterEpsilon` proves the published
[`Langlands.Conductor.TrivialCharacterEpsilonStatement`](TrivialCharacterEpsilonStatement.md)
at independent universes `uF` (the field) and `uV` (the carrier of `π`). The field
is any nonarchimedean local field, including positive characteristic. For every
irreducible admissible generic representation `π` of `GL_(n+1)(F)` (`IsGeneric ψ n π`),
with `q`, `abv`, `ϖ`, `ψ` (`HasIntegerConductor ψ`) and the self-dual `ν` as in the
statement, it gives `PairEpsilonFactorExists q ψ abv ν π (rankOneCharacter 1)`. That
is, there are `c : ℂˣ` and `m : ℤ` with
`IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`. The case `n = 0` is
included.

Mathematically this is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), Theorem (2.7), printed pages 390–391, for
`π' = 1` on `GL_1`, over the local non-archimedean ground field of section (0.3),
printed page 375. For `n = 0` it is Tate's local functional equation.

## Proof

The proof is one term:

```lean
trivialCharacterEpsilon_of_localFieldUnequalRankFunctionalEquation
  RankinSelberg.localFieldUnequalRankFunctionalEquation.{uF, uV, 0}
```

- `RankinSelberg.localFieldUnequalRankFunctionalEquation` is the published proof
  (module
  `Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationProof`)
  of the published `RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement`:
  JPSS 1983, Theorem (2.7)(iii), for unequal ranks, over every nonarchimedean local
  field. It is used at carrier universes `uV` (for `π`) and `0` (for the carrier `ℂ`
  of the trivial character).
- `trivialCharacterEpsilon_of_localFieldUnequalRankFunctionalEquation` is the helper
  theorem of the new module
  [`TrivialCharacterEpsilonReduction`](TrivialCharacterEpsilonReduction.md), which
  derives the target from that functional equation:
  - **`n = 0`.** The functional equation is not used. The published
    `conductorExponent_rankOne_of_localTate`, applied to the published proof
    `GodementJacquet.localTateConductor` of Tate's local functional equation, gives
    `c` and `a : ℕ` with `IsPairEpsilonFactor … (c, a)`. The witness is
    `(c, (a : ℤ))`.
  - **`n = m + 1`.** `π` is of Whittaker type for the standard character, by the
    published all-field multiplicity-one theorem `Whittaker.localFieldMultiplicityOne`
    and `whittakerTypeFromMultiplicity`. `rankOneCharacter 1` is of Whittaker type for
    the inverse standard character, because it is smooth. The functional equation at
    the published quotient measure `unipotentQuotientHaar F 0` and one pair of nonzero
    functionals gives the fixed-monomial equation `UnequalRankEpsilonEquation`.
    The published `unequalRankEpsilonFactor_of_equation` transports it to every
    compatible quotient measure and every pair of nonzero functionals. Then
    `isPairEpsilonFactor_of_lt` identifies the result with `IsPairEpsilonFactor`.

The final theorem has no premises. Existence of the epsilon factor, the L-factor
generators, rational continuation, the functional equation and Whittaker
multiplicity one all come from published theorems, not from hypotheses.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiles
`TrivialCharacterEpsilonReduction` and `TrivialCharacterEpsilonProof` with no errors
or warnings. `trivialCharacterEpsilon` has universe parameters `uF`, `uV` and uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.
