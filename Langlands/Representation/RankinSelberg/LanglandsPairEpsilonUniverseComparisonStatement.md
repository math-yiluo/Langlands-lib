# Carrier-universe comparison for nongeneric pair epsilon factors

Author: Worker 1799.

This module states one named comparison obligation and proves one immediate
corollary of it. It imports only
`Langlands.Representation.RankinSelberg.LanglandsFactors` and changes no
existing definition.

## Statement

`Langlands.RankinSelberg.LanglandsPairEpsilonUniverseComparisonStatement.{uF, uV, uW}`
quantifies over

- a prime `p` with `[Fact p.Prime]` and a p-adic field `F : PadicField.{uF} p`,
  with its canonical topology;
- a unitary additive character `ψ` of `F.Carrier`;
- an arbitrary additive Haar measure `ν` on `F.Carrier` for the Borel structure,
  the same binder that `LanglandsFactors` uses;
- ranks `r t : ℕ`;
- `π : SmoothRep.{0, uF, max uF uV} ℂ (GL (r + 1) F)` and
  `σ : SmoothRep.{0, uF, max uF uW} ℂ (GL (t + 1) F)`;
- a monomial `e : ℂˣ × ℤ`, where `e = (c, m)` stands for `c q^(-ms)`.

It asserts

```text
IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ e →
  IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e
```

The second and third universe parameters of `IsLanglandsPairEpsilonFactor`
are the carrier universes of the square-integrable data
`SquareIntegrableLanglandsDatum.{uV, uF}` and
`SquareIntegrableLanglandsDatum.{uW, uF}`. They are not the universes of `π`
and `σ`, which are always `max uF uV` and `max uF uW`. Lean reduces
`max uF (max uF uV)` to `max uF uV`, so the hypothesis is about the same `π`
and `σ` as the conclusion. Only the universe of the blocks changes. The
statement keeps `F`, `ψ`, `ν`, the ranks and `e`. It does not identify
different universes. It is an implication between two instances of the same
definition.

The statement does not assume that `π` or `σ` is irreducible or admissible. The
hypothesis already makes `π` and `σ` irreducible quotients of normalized
inductions. Both rank orders are allowed, as in `IsLanglandsPairEpsilonFactor`.

## Why the comparison is needed

`LanglandsFactorDescent.langlandsPairEpsilonFactorOfClassification` builds the
epsilon certificate from classification and exhaustion. It produces the
saturated instance `IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW}`,
because classification and exhaustion are stated for blocks in the saturated
universes. The principal statement of this task,
`LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}`, by Worker 1411,
concludes with the same saturated instance. The existing consumers use other
instances:

- `LanglandsGammaFactor` (`IsLanglandsPairGammaFactor`,
  `LanglandsPairGammaInput`) uses `IsLanglandsPairEpsilonFactor.{uF, uV, uW}`
  for the same `π` and `σ`.
- `Correspondence.FullFactorCompatibility` (`IsAutomorphicPairEpsilonFactor`)
  uses `IsLanglandsPairEpsilonFactor.{uF, uA, uA}` for `J` and `J'` with
  carriers in `max uF uA`.

The task contract asks to preserve independent field and carrier universes, and
to handle the saturated universes explicitly or to supply named comparison
obligations instead of identifying unequal universes. This statement is that
named comparison.

## Meaning, clause by clause

`IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e` has three clauses:

1. some `d : SquareIntegrableLanglandsDatum.{uV, uF}` of rank `r + 1` satisfies
   `d.IsLanglandsQuotient π`, that is, `π` is an irreducible quotient of the
   normalized induction `d.induced`;
2. the same holds for `σ` with some `d'` in `uW` of rank `t + 1`;
3. for all such `d` and `d'` presenting `π` and `σ`,
   `IsSquareIntegrableDataEpsilonFactor F ψ ν d d' e` holds. This means that
   there is a family `b i j` with
   `IsPadicRankEpsilonFactor F ψ ν (d.blocks i) (d'.blocks j) (b i j)` for every
   pair of blocks and `e = epsilonFactorProduct b`, the product of the
   coefficients together with the sum of the exponents.

So the comparison asserts two things. First, the data presenting `π` and `σ`
with saturated blocks give data with blocks in `uV` and `uW` (clauses 1 and 2).
Second, the universal block-product clause for all saturated data implies it
for all data in `uV` and `uW`, with the same `e` (clause 3).

## Intended proof route

The proof is not part of this statement contribution. Its exact-target proof
task can be published once this statement is public. The intended route uses
only Library results and needs no analytic input, classification, exhaustion or
cardinality hypothesis.

- Clauses 1 and 2 (smaller block universes). For a saturated datum `D`
  presenting `π`, the theorem `Langlands.padicIrreducibleSmoothSmallRealization`
  gives each irreducible smooth block `D.blocks i` an equivalent irreducible
  smooth realization `b i` with carrier in `uV`. Its proof uses the second
  countability of `GL_n(F)`. Then
  `SquareIntegrableLanglandsDatum.withBlocks D b E` is a datum in `uV` with the
  same shape. It transports irreducibility, essential square-integrability and
  the unitary exponent data along the block equivalences, and it keeps the
  exponents and therefore their antitone order. `withBlocksInducedEquiv` gives
  an equivalence of the normalized inductions. With
  `Classification.IsIrreducibleQuotient.of_equiv`, the new datum presents `π`.
  The argument for `σ` and `uW` is the same.
- Clause 3 (universal products). For data `d` in `uV` and `d'` in `uW`
  presenting `π` and `σ`, `SquareIntegrableLanglandsDatum.universeLift.{uF, uV, uF}`
  raises every block by `ULift` to `max uF uV`, again with the same shape.
  `universeLiftInducedEquiv` and `IsIrreducibleQuotient.of_equiv` show that the
  lifted data present `π` and `σ`. The saturated clause 3 then gives block
  factors `b` with `e = epsilonFactorProduct b`. Since the index types agree,
  `IsPadicRankEpsilonFactor.congr_equiv` (from `LanglandsFactorDescent`),
  applied to `SmoothRep.universeLiftEquiv` on both sides, returns each block
  factor to the original blocks. The same `b`, and therefore the same `e`,
  works for `d` and `d'`.

In the special case `uV = max uF u` and `uW = max uF u'`, the hypothesis and
the conclusion are the same proposition after universe normalization, so the
statement holds there by the identity.

## Corollary proved here

`exists_isLanglandsPairEpsilonFactor_of_universeComparison` takes the
comparison `hc` together with implicit `p`, `F`, `ψ`, `ν`, `r`, `t`, `π` and
`σ`. It turns `∃ e, IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ e`
into `∃ e, IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e`, keeping the
same `e`. The proof applies `hc` to the witness.

Take irreducible admissible `π` and `σ` and a self-dual Haar measure
`ν : SelfDualHaar F.canonicalTopologicalData ψ`. Then
`LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}` gives the hypothesis
of this corollary at `ν.val`. The comparison and the corollary then give the
epsilon component `∃ e, IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν.val π σ e`
of `LanglandsPairGammaInput.{uF, uV, uW}`. This module does not import the
principal statement, so it does not state that combination as a theorem.

## Provenance and normalization

The statement is internal and derived. It has no literature source. JPSS 1983,
(9.4), and Henniart 2002, Section 2.8, printed page 596, work with isomorphism
classes of representations and say nothing about carrier universes. The
comparison exists only because the Lean definitions fix a universe for the
blocks of the data. Its mathematical content is that the epsilon factor
defined through Langlands data depends only on the isomorphism classes of the
blocks. The normalizations are those of `IsLanglandsPairEpsilonFactor`, and
this statement leaves them unchanged: the character `ψ`, the Haar measure `ν`,
the reading of `(c, m)` as `c q^(-ms)`, the product of block monomials and the
rank-order convention of `IsPadicRankEpsilonFactor`. The comparison keeps `ψ`
and `ν` fixed, so it needs no self-duality condition on `ν`.

## Development checks

The module compiled without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection reports that the statement
returns `Prop`, has universe parameters `uF, uV, uW`, and uses only the
assumptions `propext`, `Classical.choice` and `Quot.sound`. These checks are
not independent review or Library publication.
