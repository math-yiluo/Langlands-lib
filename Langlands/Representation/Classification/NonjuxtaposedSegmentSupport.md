# The support obstruction for nonjuxtaposed segments

This internal helper implements the finite multiset argument in Zelevinsky
(1980), Proposition 4.3 and its proof in §4.5, printed pp.184–185. It proves no
representation-theoretic derivative formula. Its integral-twist-freeness
hypothesis is explicit.

For each position, `residualContent` is either the full segment content or the
content with the last member removed. A shortened singleton has empty content.
The Boolean is `true` exactly when the segment is shortened. `content` sums
these multisets over all positions, preserving every occurrence.

Adding a segment's beginning to its positively twisted residual content gives
its original content, together with its positively twisted end when it was
not shortened. The two identities used here are the published
`SegmentContentShift.lower_content` and `content_map_twist_add_base`.
Summing and cancelling the original content shows that the shifted ends of
the unshortened positions are contained in the multiset of all beginnings.
Thus each unshortened position has a shifted end equal to some beginning.
Integral twist freeness excludes its own beginning.

`isJuxtaposed_of_base_eq_last_twist` establishes that such equality at another
position gives actual juxtaposition directly from the segment definitions.
Integral twist freeness makes the first segment's natural-index member map
injective. The second segment's member at `j` is the first segment's member
at `length(Δ)+j`, so their supports are disjoint. A segment with the first
base and length `length(Δ)+length(Γ)` realizes the support union: split its
member indices at `length(Δ)`. Disjointness and the nonempty supports exclude
containment in either direction, completing the linkage and juxtaposition.
`all_shortened_of_map_twist_le` consequently proves that every position was
shortened whenever distinct positions are not juxtaposed and the positive
unit twist of the residual multiset is contained in the original content.
`sum_orders_eq_sum_ranks` rewrites the resulting sum of Boolean-selected ranks
as the sum of all segment ranks.

The universe parameters `uF` and `uV` remain independent. No field topology
instance or additive character is chosen: the proof concerns the actual
published segment and cuspidal-datum types. It uses the positive twist
`CuspidalDatum.twist 1` throughout. Repeated or equal segments and arbitrary
orderings are allowed.

## Dependencies and independence

The single direct import is the published `SegmentContentShift`. Its
`lower_content`, `content_map_twist_add_base`, and `base_ne_last_twist`
are reused by Lean name. The endpoint-to-juxtaposition proof above uses only
the original segment definitions and twist composition; it imports neither
`SegmentIntegralCoordinates` nor `SegmentIntervalLinkage`.

A full recursive import traversal against Library commit
`546440987a08c6f0a563446add611f8ff5c9a372` finds 54 project modules including
this new module, with no missing project imports and no modifications to the
53 imported project files. The classification modules in that closure are
`ConstituentRelations`, `Supercuspidal`, `SupercuspidalTwist`, `Segments`,
`SegmentCuspidalContent`, `CuspidalIntegralTwistFreenessStatement`,
`SegmentContentShift`, and this module. The remaining project modules provide
the underlying field, topology, groups, smooth representations, induction,
tensor products, Jacquet coinvariants, and twists. No derivative formula,
support-extraction theorem, or product classification theorem is used.
Freeness is a proposition supplied to the lemmas, not an assumed new axiom.

In particular the direct and transitive closure uses none of the following
excluded conclusions or their proofs:

- `UnlinkedSegmentSocleProductIrreducible`,
  `LinkedSegmentSocleReverseProductStructure`, and
  `LinkedSegmentSoclePairReducible`.
- `JuxtaposedSegmentSocleReverseProductStructure` and
  `LinkedSegmentSocleReverseProductQuotientHom`, with their proofs.
- `SegmentSocleProductIrreducibility`.
- `AdjacentUnlinkedSegmentSocleSwap`.
- `TwoSegmentSocleCommutation`.
- `LinkedSegmentSocleGluing`.
- `OrderedMultisegmentSocleExistence`, socle exhaustion
  (`MultisegmentSocleExhaustion`), and segment analytic
  classification (`SegmentEssentialSquareIntegrableClassification`).
- Special-head multisegment exhaustion (`MultisegmentHeadExhaustion`),
  ordered special-head existence (`OrderedMultisegmentHeadExistence`),
  quotient coverage (`OrderedMultisegmentQuotientExhaustion`), ordered
  conversion, and tempered block uniqueness (`TemperedBlockUniqueness`).
- `GenericSegmentProductUniqueness` and
  `SquareIntegrableLanglandsClassification`.
- Square-integrable exhaustion (`SquareIntegrableLanglandsExhaustion`),
  regular exhaustion (`GLRegularLanglandsExhaustion`), and forward
  special-segment essential square-integrability.
- `SegmentHeadProductIrreducibility` and its conclusions.

This module is the combinatorial helper for the proof of
`NonjuxtaposedSegmentSocleConstituentLevel`. The support containment premise
and segment-derivative selection are proved separately for the actual
representation in `NonjuxtaposedSegmentSocleConstituentLevelProof`, which
applies `sum_orders_eq_sum_ranks` to obtain the exact constituent-level
theorem.
