# Proof of Henniart's separation by square-integrable pole orders

Author: Worker 4836.

`Langlands.RankinSelberg.squareIntegrablePoleOrderCharacterization.{uF, uV, uW}`
proves the published proposition
`Langlands.RankinSelberg.SquareIntegrablePoleOrderCharacterizationStatement.{uF, uV, uW}`
of `PairLFactorCharacterizationStatement`. The three universes are independent.
The theorem's type is that proposition. It adds no hypothesis.

Henniart 2002, Théorème 1.7(b), printed page 591, states the mathematics. Let
`π` and `π'` be irreducible admissible representations of `GL_N(F)`, `N ≥ 2`,
with `π` not supercuspidal. Suppose that for every irreducible essentially
square-integrable `ρ` of `GL_r(F)`, `1 ≤ r ≤ N - 1`, the factors
`L(s, π × ρ)` and `L(s, π' × ρ)` have poles of the same order at `s = 0`.
Then `π ≃ π'`. In the Library statement, `N = n + 2`, the test ranks are
`r + 1` for `r ≤ n`, and the factors are given as certificates of
`IsLanglandsPairLPolynomial`. Pole order means `lPolynomialPoleOrderAtZero`.

## Implemented proof

The proof is a term. It applies the published reduction
`squareIntegrablePoleOrderCharacterization_of_classification` of
`SquareIntegrablePoleOrderCharacterizationReduction`. That reduction carries
out Henniart's §4 argument: pole orders count the segment links of the
multisegment of `π`, these counts determine the multisegment, and equal
multisegments give isomorphic representations. It takes five prerequisites
as hypotheses. The proof supplies each one with a proved Library theorem:

1. `hE`, the square-integrable Langlands exhaustion, for every `p` and `F` with
   its canonical topological data:
   `Classification.squareIntegrableLanglandsExhaustion.{uF, uV}`.
2. `hC`, the square-integrable Langlands classification (Henniart 2002, §2.8),
   for every `p` and `F`:
   `Classification.squareIntegrableLanglandsClassification.{uF, uV}`.
3. `h95`, JPSS 1983, Theorem (9.5), in product form:
   `SquareIntegrableDataLFactorStatement.{uF, uV, uW}`. The auxiliary theorem
   `squareIntegrableDataLFactor`, imported from
   `SquareIntegrableDataLFactorProof`, proves it. See below.
4. `hSH`, Henniart 2002, §2.6, at universes `{uF, max uF uV, max uF uV}`:
   `segmentHeadLFactor_of_squareIntegrable squareIntegrableLFactor
   squareIntegrableLFactor`. The reduction `segmentHeadLFactor_of_squareIntegrable`
   needs JPSS 1983, Theorem (8.2), in two universe orders. Both are instances
   of the proved, universe-polymorphic `squareIntegrableLFactor`.
5. `h81`, JPSS 1983, Proposition (8.1)(ii), at universes
   `{uF, max uF uV, max uF uV}`: `supercuspidalEqualRankLFactor`.

## The auxiliary theorem

`squareIntegrableDataLFactor : SquareIntegrableDataLFactorStatement.{uF, uV, uW}`
is defined in the focused `SquareIntegrableDataLFactorProof` module, with the same
public name and statement. It applies the published reduction
`squareIntegrableDataLFactor_of_prerequisites`
of `SquareIntegrableDataLFactorReduction` to these proved theorems:

- equal-exponent grouping, for every `p` and `F`, in the pairs `{uF, uV}` and
  `{uF, uW}`: `Classification.squareIntegrableEqualExponentGrouping`;
- JPSS 1983, Proposition (8.4), at `{uF, max uF uV, max uF uW}`:
  `temperedLFactor`;
- JPSS 1983, Proposition (9.4), display (3), at `{uF, max uF uV, max uF uW}`:
  `langlandsTypeLFactor`;
- regular tempered Langlands data uniqueness in the pairs `{uF, uV}` and
  `{uF, uW}`: `Langlands.glRegularLanglandsDataUniqueness`.

The theorem is exactly the existing Library proposition. It is stated
separately so that other developments can import it.

## Checks

`lean_check` of the module reports no errors and no warnings. The axioms of
`squareIntegrablePoleOrderCharacterization` are `propext`, `Classical.choice`
and `Quot.sound`.

## Dependencies

The original proof used published prerequisites from Library commit 200fd1a4.
It now imports `SquareIntegrableDataLFactorProof` for the consolidated auxiliary
theorem. Its other prerequisites are:
`SquareIntegrablePoleOrderCharacterizationReduction`,
`TemperedLFactorProof`,
`LanglandsTypeLFactorProof`, `SquareIntegrableLFactorProof`,
`SegmentHeadLFactorReduction` and `SupercuspidalEqualRankLFactorProof` under
`Langlands/Representation/RankinSelberg`, and
`SquareIntegrableLanglandsExhaustionProof`,
`SquareIntegrableLanglandsClassificationProof`,
`SquareIntegrableEqualExponentGroupingProof` and
`RegularLanglandsDataUniquenessProof` under
`Langlands/Representation/Classification`. The theorem names and mathematical statements are unchanged by this organization.
