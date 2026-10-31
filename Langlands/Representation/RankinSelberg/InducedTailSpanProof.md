# The three direct-rank induced tail Laurent-span inclusions

Author: Worker 53.

`Langlands.RankinSelberg.inducedTailSpan.{uF,uV₁,uV₂,uW}` proves the existing
closed proposition
[`InducedTailSpanStatement`](InducedTailSpanStatement.md).
The proof constructs its conjunction in the definition's order from three
published closed theorems, each at the original four independent universes:

| Clause | Imported theorem | Rank condition |
| --- | --- | --- |
| Equal tail and test ranks | [`inducedTailEqualRankSpan`](InducedTailEqualRankSpanProof.md) | `T = B` |
| Smaller test rank | [`inducedTailSmallerRankSpan`](InducedTailSmallerRankSpanProof.md) | `T < B` |
| Intermediate test rank | [`inducedTailIntermediateRankSpan`](InducedTailIntermediateRankSpanProof.md) | `B < T < A+B` |

Here `A` and `B` are the positive ordered block ranks, `T` is the positive
test rank, and the full representation is the target's literal
ULift-conjugated canonical normalized upper two-block induction. Each clause
includes the actual tail Laurent span in the actual full zero-row Laurent
span. The intermediate clause retains the canonical larger-first tail
`(σ, π₂)` with the same specified additive character as the full pair.
The component proofs supply its inverse-character and compatible-measure
transports, integrability, rational-continuation comparisons, and nonzero
volume-scalar removal; this wrapper adds no analytic construction.

The conjunction preserves every field, character, supplied self-dual Haar
measure, arbitrary Whittaker-type block and test representation, actual
rectangular product measure, and independently compatible quotient measure
quantified by its three clauses. The proof has no premises. In particular,
it requires no certified L-polynomial or additional representation hypothesis.
The statement pair and its imported pairs are unchanged by this contribution.

This is an internal composition of the three imported Library proofs.
Workers 646 and 647 authored the equal and smaller comparisons, with
contributions recorded in their paired explanations; Workers 318 and 829
authored the intermediate construction and assembly. Their explanations
document the derived direct-rank argument motivated by JPSS, *Rankin-Selberg
Convolutions* (1983), §§9.1–9.3, printed pp.452–457, and the registered
original and source checks. This wrapper makes no new source translation
claim.

The aggregate covers the three direct-rank cases below the full induced
rank. It does not assert a certified polynomial's existence or a
polynomial-divisibility conclusion; the parent all-rank theorem additionally
requires the separately owned factor-existence, opposite-bound and
high-ramification inputs.
