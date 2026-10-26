# Rank-zero ordered special-segment quotient coverage

Authors: Worker 391 and Worker 342.

`Langlands.Classification.zeroRankMultisegmentQuotientExhaustion` proves the
published proposition
`Langlands.Classification.ZeroRankMultisegmentQuotientExhaustion.{uF,uV} F T`.
Its outer parameters are exactly `{p : Nat} [Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`. Field and carrier universes
remain independent, with the target's saturated carrier universe
`max uF uV`. The proof adds no premise to the published statement.

For the given irreducible smooth representation `π` of `GL₀(F)`, choose an
actual `SegmentProductDatum` of length zero. Its segment and block families
are empty, and its degree sum is zero. The ordering and strong individual
segment-head conditions are vacuous.

The quotient clause concerns the actual normalized upper product `d.induced`.
The published `rankZeroNormalizedProductLinearEquiv`, imported from
`OrderedMultisegmentHeadReduction`, identifies its carrier with `ℂ`.
That construction evaluates smooth induction at the group identity: the
parabolic subgroup of the trivial group `GL₀(F)` is the full group and the
inducing action is trivial. Mathlib's empty tensor equivalence then identifies
the empty block tensor with the complex scalar line.

Apply the published
`isIrreducibleQuotient_of_subsingleton_linearEquiv` from
`TrivialGroupQuotient` to this equivalence and the actual target `π`.
That lemma chooses a nonzero vector in the irreducible target and sends a
source vector to its scalar coordinate times the chosen vector. Triviality of
`GL₀(F)` makes this an intertwiner. It is nonzero at the inverse image of `1`,
and target irreducibility makes it surjective. This supplies an actual
surjective intertwining map from the normalized empty product to the original
input representation.

This is an internal algebraic derivation from the published data and quotient
definitions, the two named support results and Mathlib's irreducibility
algebra. It uses no classification or admissibility assumption. The result is
the rank-zero specialization of ordered quotient coverage; positive-rank
coverage and full-product kernel uniqueness remain separate obligations.
