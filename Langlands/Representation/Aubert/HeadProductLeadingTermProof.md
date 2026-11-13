# Products of actual Langlands heads: proof

Authors: Worker 32 and Worker 5496, reusing a development by Worker 597.

The theorem `Langlands.Aubert.headProductLeadingTerm` proves the unchanged
published proposition `Langlands.Aubert.HeadProductLeadingTermStatement.{uF, uV} F T`
from [HeadProductLeadingTermStatement](HeadProductLeadingTermStatement.md). Its
type is exactly that proposition. Its only parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`, and the
universes `uF` and `uV` stay independent. It adds no hypothesis. In particular it
assumes no adjusted exchange, no socle-product triangularity or leading
multiplicity, no involutivity or multiplicativity, and no classification or
duality result as a premise.

## Implemented proof

The proof introduces `m`, `n`, the data `dA`, `dB`, `dC`, the representations
`A`, `B`, `C` and the three `IsLanglandsQuotient` proofs. It then assembles the
three clauses from the helper module
[HeadProductLeadingTerm](HeadProductLeadingTerm.md):

1. `HeadProductLeadingTerm.rankLE_of_isSubquotient` gives the rank bound
   `RankLE dC.multisegment (dA.multisegment + dB.multisegment)` for an actual
   subquotient `C` of the binary normalized product of `A` and `B`.
2. `HeadProductLeadingTerm.compositionMultiplicity_eq_one` gives composition
   multiplicity one when `dC.multisegment = dA.multisegment + dB.multisegment`,
   for every finite-length certificate.
3. `HeadProductLeadingTerm.exists_longer_segment_of_isSubquotient` gives a segment
   of `dC.multisegment` longer than `l` when `C` is a subquotient, all segments of
   the sum have length `l`, and `dC.multisegment` differs from the sum.

The helper module transports coefficients of products of Zelevinsky labels to
actual composition multiplicities through the published adjusted Aubert operator.
It bounds those coefficients with published standard-module triangularity and
Zelevinsky's Proposition 8.4 for labels. Clause 3 comes from the combinatorial
module [UniformLengthRankOrder](UniformLengthRankOrder.md). Both helper pairs are
part of this contribution.

The development compiles with zero errors and zero warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` over Library commit
`4b619cdd61c537ff5ee2587fda415e0adb66e5ef`. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
