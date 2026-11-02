# Ordered cuspidal members of a segment product

This module contains the existing ordered-member infrastructure extracted from
`SegmentProductCuspidalEmbedding`. All public declarations retain their names in
`Langlands.Classification.SegmentProductCuspidalEmbedding`, their types and their
implementations. Both the segment-socle embedding and the segment-head quotient
import it, so the quotient needs no derivative or finite-length infrastructure.

The field and base-representative universes remain independent. For a supplied
`d : T.SegmentProductDatum.{uV, uF} n`, every segment occurrence and every
member occurrence is retained. This module makes no irreducibility assertion.

### The members of a segment product

- `ofFn_multiset_eq_sum f`: the multiset of `List.ofFn f` is
  `∑ i, {f i}`.
- `memberRefinement d` (definition): the block refinement of `d.shape` that
  splits block `j` uniformly into `(d.segments j).length` blocks of rank
  `(d.segments j).rank`.
- `memberFamily d` (definition): all members of all segments, in order. It is
  indexed by the blocks of the flattened shape, and entry `(j, i)` is
  `(d.segments j).member i`. `memberFamily_sum`: their ranks add up to `n`.
- `memberRepresentatives d A` (definition): given supercuspidal representatives
  `A j` of the bases of the segments, entry `(j, i)` is the published twist of
  `A j` by `|det|^i`. `memberRepresentatives_represent`: if each `A j`
  represents `(d.segments j).base`, then entry `(j, i)` represents
  `(d.segments j).member i`.
- `memberInducedIso d A`: the supercuspidal product of all members is
  isomorphic to the normalized product over `d.shape` of the segment inductions
  `T.segmentInduced (A j).obj (d.segments j).length _`, i.e. of
  `A_j × ν A_j × ⋯ × ν^(m_j - 1) A_j` with `m_j = (d.segments j).length`. Proof: the published ordered regrouping
  isomorphism `Parabolic.orderedProductRegrouping` (induction in stages),
  followed by blockwise identifications.
- `memberFamily_content d`: the multiset of `memberFamily d` is
  `d.multisegment.cuspidalContent`.

## Provenance

These helpers were published by Worker 1070 with the following attribution,
retained from their original companion:

- The section "The members of a segment product" (`ofFn_multiset_eq_sum`,
  `memberRefinement`, `memberFamily`, `memberFamily_sum`,
  `memberRepresentatives`, `memberRepresentatives_represent`, the private
  `memberRankIso`, `memberInducedIso` and `memberFamily_content`) is adapted
  from the private helpers of the same names in
  `Langlands/Representation/Classification/SegmentHeadProductCuspidalSupportProof.lean`
  (lines 21–134 at Library commit `a9fde216`). That module is by Worker 328,
  with a rank-transport pattern adapted from Worker 627 (its Markdown records
  both). The proofs are unchanged. The changes are: the declarations are
  public (except `memberRankIso`), `F` and `T` are implicit arguments (except
  `T` in `memberRankIso`), and the
  datum is `SegmentProductDatum.{uV, uF}` with representatives
  `SupercuspidalRep.{uF, uV}`, instead of the carrier universe `max uF uV`.
  The source helpers are private, so they cannot be imported.
