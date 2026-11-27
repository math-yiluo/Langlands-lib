# The pure-stratum approximation theorem from (2.3.11), (2.3.4) and (2.3.12)

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, (2.4.1)(i), printed p. 65 (PDF p. 77), with its proof, printed pp. 66–71 (PDF pp. 78–83).

## Statements

- `maximalCriticalApproximation_of_premises hTop hRef hRefE hSplit : MaximalCriticalApproximationStatement`, the critical full-degree case.
- `pureStratumSimpleApproximation_of_premises hTop hRef hRefE hSplit : PureStratumSimpleApproximationStatement`, the Library target.

The hypotheses are the Library propositions `TopNonsplitPremise` ((2.3.11)), `NonsplitRefinementPremise` ((2.3.4)) and `SplitObstructionPremise` ((2.3.12)). (2.3.4) is used twice: at the universes of `F` and `V` for the first approximation (2.4.3), and at the universe of `V` for fields generated inside `End_F(V)` in the final step. The universes of `F` and `V` are independent. This module does not prove these three propositions.

## Proof

`maximalCriticalApproximation_of_premises` follows `maximalCriticalAssembly` (module `PureStratumApproximationAssembly`) step for step; steps 2 and 3 below differ from it.

1. `candidateSeed` gives a candidate (BK93 (2.4.3)). `optimalCandidate` chooses one, `T₀`, of maximal degree and then minimal normalized depth.
2. The derived stratum `D` of `β − T₀.b` is formed as in that module. If some element of `D.coset` differs from a scalar of `F[T₀.b]` by a nilpotent element, the proved `chainImprovement` ((2.4.5)) gives a candidate of the same degree and smaller normalized depth, which is a contradiction. The assembly instead takes (2.4.5) as a premise.
3. Otherwise `D` is fundamental, and it is not split by `SplitObstructionPremise`. `improvement_or_increase` (module `PureStratumApproximationFinalStep`) replaces the premise `DegreeIncreasePremise` of the assembly. Its first alternative is again a candidate of the same degree and smaller normalized depth, a contradiction. Its second alternative is exactly the conclusion of `DegreeIncreasePremise`, and the rest of the proof is that of `maximalCriticalAssembly`: maximality of the degree, `maximalSimpleReflection`, `stratumEquivalence` (BK93 (1.5.2), (2.1.4)), `lineChainTranslation` and `chainTranslation`.

`pureStratumSimpleApproximation_of_premises` composes this with `pureStratumApproximationMaximalReduction` and `pureStratumApproximationCriticalReduction`. The proof uses finite heartbeat limits for elaboration with generated-field instances, as in the assembly. It does not use (2.4.1)(iii), the aggregate theorem `StratumApproximationStatement`, or `DegreeIncreasePremise`.
