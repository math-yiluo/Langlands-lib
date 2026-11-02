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
excluded conclusions or their proof successors:

- `UnlinkedSegmentSocleProductIrreducible`,
  `LinkedSegmentSocleReverseProductStructure`, and
  `LinkedSegmentSoclePairReducible` (tasks
  `23e98d90-6055-4e35-91a9-b0f5d8a84961`,
  `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`,
  `8fa9f68b-fa1b-431a-97f6-5b163964d1fc`).
- `JuxtaposedSegmentSocleReverseProductStructure` and
  `LinkedSegmentSocleReverseProductQuotientHom`
  (`7ff2a1e9-89dc-439e-a861-a567b3db92bf` and its proof successors).
- `SegmentSocleProductIrreducibility`
  (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`).
- `AdjacentUnlinkedSegmentSocleSwap`
  (`e3634665-571b-4852-9f4c-bab8a1053434`,
  `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`).
- `TwoSegmentSocleCommutation`
  (`426911b4-6620-413f-8065-04b25287f3bd`,
  `66e3b87c-647e-41e4-af18-df4d436765f0`).
- `LinkedSegmentSocleGluing`
  (`c84cd52c-3ff3-4024-be50-8b84dd480888`,
  `6780b79c-9526-46aa-b8b4-00377d68b1ea`).
- `OrderedMultisegmentSocleExistence`
  (`23189526-80b0-4828-a6d4-7ebec2cbeef5`), socle exhaustion
  (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`), and segment analytic
  classification (`aca8805b-054f-4d56-8045-12db7f623404`).
- Special-head multisegment exhaustion
  (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered special-head existence
  (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage
  (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), ordered conversion
  (`8252833d-c269-41a9-824c-5879e531b23b`), and tempered block uniqueness
  (`52e97845-36bb-457d-b76f-70753334b88c`).
- `GenericSegmentProductUniqueness`
  (`30341ae4-65f2-4a0e-9283-763db01a409e`) and
  `SquareIntegrableLanglandsClassification`
  (`1cb45da2-7007-4351-a694-594fb148b8d1`).
- Square-integrable exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`),
  regular exhaustion (`bf433f0a-921a-428c-b0c0-6475438125ac`), and forward
  special-segment essential square-integrability
  (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`).
- `SegmentHeadProductIrreducibility`
  (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`) and its conclusions.

This contribution is the combinatorial helper for task
`60b25b28-1377-458d-9bd0-4072917d4581`. The support containment premise
and segment-derivative selection must be proved separately for the actual
representation before it yields the task's exact constituent-level theorem.
