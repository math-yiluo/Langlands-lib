# Proof of the rank-one extension span comparison

Module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonProof`.

The theorem `rankOneExtensionSpanComparison` proves the published proposition
`RankOneExtensionSpanComparisonStatement.{uF, uV, uW}` of
[RankOneExtensionSpanComparisonStatement](RankOneExtensionSpanComparisonStatement.md),
with no further hypotheses. That proposition is the case `t + 3 ≤ r + 1` of Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983),
Lemma (5.5), printed pp. 423–427. The Laurent span of the block-one integrals of the base
pair is contained in the Laurent span of the block-zero integrals of the lower induction.

## Proof

The proof is one application:

`rankOneExtensionSpanComparison_of_statements lowerBlockQuotientDisintegration
rankOneExtensionLowerJacquetFunctional`.

- `rankOneExtensionSpanComparison_of_statements` is in
  [RankOneExtensionSpanComparisonAssembly](RankOneExtensionSpanComparisonAssembly.md). It
  derives the statement from two hypotheses, `LowerBlockQuotientDisintegrationStatement` and
  `RankOneExtensionLowerJacquetFunctionalStatement`. That module describes the unfolding
  computation of the source and the constant `C ρ(U')`.
- `lowerBlockQuotientDisintegration` is the published proof of
  `LowerBlockQuotientDisintegrationStatement`, in
  [LowerBlockQuotientDisintegrationProof](LowerBlockQuotientDisintegrationProof.md).
- `rankOneExtensionLowerJacquetFunctional` is the published proof of
  `RankOneExtensionLowerJacquetFunctionalStatement`, in
  [RankOneExtensionLowerJacquetFunctionalProof](RankOneExtensionLowerJacquetFunctionalProof.md).

The universes match: `uF` is shared by all three propositions, `uW` is the universe of the
Jacquet functional statement's inducing carrier, and `uV` is the universe of the test
representation.
