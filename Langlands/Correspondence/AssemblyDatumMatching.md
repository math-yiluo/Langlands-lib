# Recovering datum matching from datum existence and classification

Author: Worker 584.

This internal supporting module connects the two existing datum interfaces used
by the assembly reductions. It assumes
`MultisegmentHeadDatumExistence.{uF, uA} F` and the published proposition
`Classification.SquareIntegrableLanglandsClassification.{uF, uA}
F F.canonicalTopologicalData`. It proves
`MultisegmentHeadDatumMatching.{uF, uA} F`. The existence and classification
premises remain explicit; neither is proved in this module.

`AssemblyDatumMatchingReductionStatement.{uF, uA} F` is the Prop-valued
definition of precisely this implication. The theorem
`multisegmentHeadDatumMatching_of_existence_and_classification` proves it
with the two premises written as explicit arguments.

`IsSegmentHeadModel.of_rankEquiv` transports a segment-head model along an
equality of ranks and a genuine equivalence of representations. After removing
the rank equality, the proof composes that equivalence with the equivalence to
the witnessed segment head.

The private helper `blockEquivOfUniverseLiftIso` recovers an equivalence of
original block actions from an isomorphism between their universe lifts,
including a rank equality. It composes the actual equivalence from each block
to its lift with the equivalence underlying the supplied isomorphism. It does
not identify different fixed-universe categories.

`multisegmentHeadDatumMatching_of_existence_and_classification` first obtains
one presenting datum `d0` and its matching permutation from the supplied
existence premise. This also supplies the existence conjunct of the conclusion.
For any other presenting datum `d`, the positive-rank case lifts both families
of blocks to universe `max uF uA`. The published
`SquareIntegrableLanglandsDatum.universeLiftInducedEquiv` and
`Classification.IsIrreducibleQuotient.of_equiv` transport their quotient
relations. The supplied classification, applied to the identity isomorphism
of their common quotient, gives a permutation and actual isomorphisms between
the lifted blocks. The private helper returns equivalences of the original
blocks, and `IsSegmentHeadModel.of_rankEquiv` transports the models of `d0`
to the blocks of `d`. Composing the two permutations gives the required
matching with the original segments.

At rank zero, `GeneralLinear.BlockShape.length_le` makes both block-index
types empty. Their equivalence composes with the existence premise's
permutation, and the universal block condition follows because there is no
block index. The classification premise is used only at positive rank,
exactly within its stated domain.

`assemblyEpsilonInheritance_of_datumExistence_classification_and_segmentPairs`
passes this matching result to the published remaining assembly reduction.
It retains datum existence, square-integrable classification, and
`SupercuspidalSegmentPairInheritance.{uF, uP, uA} F` as explicit premises.
The field, parameter, and automorphic carrier universes remain independent.
The original assembly target, its single witnessed local-constant system,
and its additive-character and self-dual-measure quantifiers are unchanged.
This corollary is not an unconditional proof of the host assembly target.

The provenance is direct composition of the imported Library interfaces and
their actual transport constructions. No external source assertion is added.
