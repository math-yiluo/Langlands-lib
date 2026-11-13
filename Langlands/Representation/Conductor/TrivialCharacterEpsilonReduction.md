# Reduction of the trivial-character epsilon factor to the all-field functional equation

Author: Worker 5550. This internal helper module proves
`Langlands.Conductor.TrivialCharacterEpsilonStatement.{uF, uV}` from one premise,
the separately stated
`Langlands.RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement.{uF, uV, 0}`
([`LocalFieldUnequalRankFunctionalEquationStatement`](../RankinSelberg/LocalFieldUnequalRankFunctionalEquationStatement.md)).
This module keeps it as a premise. The premise is discharged in
[`TrivialCharacterEpsilonProof`](TrivialCharacterEpsilonProof.md) by the published
all-field proof `Langlands.RankinSelberg.localFieldUnequalRankFunctionalEquation`.
Every other input is a published theorem. The reduction retains arbitrary nonarchimedean local fields, including
positive characteristic, and independent universes for the field and the carrier
of `π`.

## Declarations

- `rankOneCharacter_one_isSmooth`: the trivial character `rankOneCharacter 1` of
  `GL_1(F)` is smooth. Every vector is fixed by the open subgroup `⊤`, because the
  action is multiplication by `1`.
- `rankOneCharacter_one_isOfWhittakerType_inverse`: `rankOneCharacter 1` is of
  Whittaker type for `inverseStandardCharacter ψ 0`. The published
  `scalar_isOfWhittakerType_rankOne` gives Whittaker type for the standard
  character from smoothness, and the published
  `isOfWhittakerType_standard_iff_inverse` changes the character.
- `isOfWhittakerType_of_isGeneric_localField`: over every nonarchimedean local
  field, `IsGeneric ψ r π` implies `IsOfWhittakerType r (standardCharacter ψ r) π`.
  `IsGeneric` gives irreducibility, admissibility and a nonzero standard
  functional `ℓ`. The published all-field multiplicity-one theorem
  `Whittaker.localFieldMultiplicityOne` writes every functional as a multiple of
  `ℓ`, and the published `whittakerTypeFromMultiplicity` concludes.
- `trivialCharacterEpsilon_of_localFieldUnequalRankFunctionalEquation`: the
  reduction itself.

## Proof of the reduction

After introducing the binders of `TrivialCharacterEpsilonStatement`, the proof
splits on the rank `n + 1` of `π`.

- **`n = 0`.** No premise is used. The published
  `conductorExponent_rankOne_of_localTate`, applied to the published proof
  `GodementJacquet.localTateConductor` of `LocalTateConductorStatement`, gives
  `c : ℂˣ` and `a : ℕ` with
  `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, a)` (and newvector
  facts, discarded). The witness is `(c, (a : ℤ))`.
- **`n = m + 1`.** Here `0 < m + 1`, so the pair relation is the unequal-rank one.
  `π` is of Whittaker type by `isOfWhittakerType_of_isGeneric_localField`, and
  `rankOneCharacter 1` by `rankOneCharacter_one_isOfWhittakerType_inverse`.
  `IsOfWhittakerType.exists_ne_zero` supplies nonzero functionals `ℓ` and `ℓ'`.
  The premise is applied at the field `F` with ranks `0` and `m + 1`, the given
  `q`, `abv`, `ϖ`, `ψ` and `ν`, the published quotient measure
  `unipotentQuotientHaar F 0` with its compatibility
  `unipotentQuotientHaar_isCompatible F 0` (the right-invariance instance is the
  published `unipotentHaar_isMulRightInvariant`), carriers `V` and `ℂ`, and the
  pair `(π, rankOneCharacter 1)` with `ℓ`, `ℓ'`. It yields
  `UnequalRankFunctionalEquationConclusion`. The published
  `exists_unequalRankEpsilonEquation_iff` extracts `c`, `k` and the fixed-monomial
  equation `UnequalRankEpsilonEquation`. The published
  `unequalRankEpsilonFactor_of_equation` transports this equation, at one measure
  and one functional pair, to every compatible quotient measure and every pair of
  nonzero functionals, giving `IsUnequalRankEpsilonFactor`. Finally the published
  `isPairEpsilonFactor_of_lt` identifies it with `IsPairEpsilonFactor`, so the
  witness is `(c, k)`.

The premise is used at the carrier universes `uV` (for `π`) and `0` (for `ℂ`),
hence the instance `.{uF, uV, 0}`.

## Scope

The premise is the unequal-rank functional equation of JPSS 1983, Theorem
(2.7)(iii), over every nonarchimedean local field. The target's contract counts an
implication that keeps the functional equation as a premise as no proof of the
target. This module is accordingly only the reduction step. The unconditional
theorem `Langlands.Conductor.trivialCharacterEpsilon` in `TrivialCharacterEpsilonProof`
applies it to the published proof of the premise. Whittaker multiplicity one is not
a premise here; it is the published `localFieldMultiplicityOne`. The equal-rank case
`n = 0` is unconditional.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiles the
module with no errors or warnings. The reduction theorem uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
