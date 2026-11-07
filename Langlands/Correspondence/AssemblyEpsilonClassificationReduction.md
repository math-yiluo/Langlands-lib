# Epsilon inheritance from classification and the segment-head L formula

This module removes from the conditional epsilon-inheritance reduction every
premise that the Library now proves. Two premises remain explicit.

## Discharged premises

- `Langlands.Correspondence.blockPairGamma` proves the published block-pair
  gamma law `LocalFactor.PairBlock.BlockPairGamma.{uF, uP} F` (Henniart 2002,
  §2.4) without hypotheses. It applies
  `LocalFactor.CommonClosureGamma.blockPairGamma_of_wdEulerPairBlock`
  (module `Langlands.Correspondence.BlockPairGammaReduction`) to the proved
  pair-block Euler formula `LocalFactor.wdEulerPairBlock`, used at the
  universes `{0, uF, max uF uP, max uF uP}`.
- The segment-head gamma formula is the proved theorem
  `RankinSelberg.segmentHeadGammaFactor`, used at `{uF, uA, uA}`.
- Datum matching `MultisegmentHeadDatumMatching.{uF, uA} F` is obtained from
  `multisegmentHeadDatumMatching_of_existence_and_classification`. That
  theorem takes the proved datum existence `multisegmentHeadDatumExistence`
  and the classification premise below.
- The pair-block Euler formula is used a second time, at `{0, uF, uP, uP}`.
  This instance is the only explicit Euler premise `hE` of
  `assemblyEpsilonInheritance_of_segmentHeads` (module
  `Langlands.Correspondence.SegmentEpsilonInheritance`). The first use, at
  `max uF uP`, is inside `blockPairGamma`, which supplies that theorem's
  separate block-pair gamma premise `hBPG`.

## Remaining premises

`AssemblyEpsilonClassificationReductionStatement.{uF, uP, uA} F` is the
implication

- `Classification.SquareIntegrableLanglandsClassification.{uF, uA} F
  F.canonicalTopologicalData` (the square-integrable Langlands
  classification), and
- `RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}` (Henniart 2002,
  §2.6, the L-factor formula for pairs of segment heads)

imply `AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F`. The parameter
and automorphic carrier universes `uP` and `uA` stay independent.

Both premises are reduced further elsewhere in the Library, and this module
uses neither reduction:
`Classification.squareIntegrableLanglandsClassification_of_regular` derives
the first from four premises: `SquareIntegrableEqualExponentGrouping`,
`TemperedBlockUniqueness`, `GLRegularLanglandsHeadExistenceStatement` and
`GLRegularLanglandsDataUniquenessStatement`. Separately,
`RankinSelberg.segmentHeadLFactor_of_squareIntegrable` derives the second
from `SquareIntegrableLFactorStatement` (JPSS 1983, Theorem (8.2)) at two
universe orders, which coincide at `{uF, uA, uA}`.

`assemblyEpsilonInheritance_of_classification_of_segmentHeadL` proves this
implication. It feeds the datum matching above, `hL`, the proved gamma
formula, `blockPairGamma F` and the Euler formula into
`assemblyEpsilonInheritance_of_segmentHeads`.
`assemblyEpsilonClassificationReduction` restates it as the named
proposition.

## Provenance

This is an internal composition of published Library theorems. It adds no
literature claim, and it does not prove the classification or the
segment-head L formula.
