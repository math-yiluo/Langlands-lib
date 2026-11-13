# The merged segment datum

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiDatum`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`).

For a segment datum `c` and a merge grouping `m` of its segments, with degrees the
segment degrees (`A6iiMerge`):

- `mergedRefinement c m`: the refinement of the group shape by segment degrees.
  `mergedLabel c m k` is the segment of `c` in flattened position `k`.
- `merged c m`: the datum listing the segments and blocks of `c` group by group. Its
  shape is literally the flattened group shape (`merged_shape`, by `rfl`).
- `mergedEquiv`: the bijection of positions; `mergedEquiv_apply` holds by `rfl`.
- `merged_multisegment`: the merged datum has the multisegment of `c`.
- `merged_hasSegmentHeads`: segment heads survive merging.
- `merged_isPrecedenceOrdered`: if the merge exponents are chosen unitary exponents of
  heads, the merged datum is precedence-ordered. Its exponents decrease
  (`MergeGrouping.antitone_exponent`), so `isPrecedenceOrdered_of_antitone` applies.
- `concatenate_multisegment`: the multisegment of the published
  `SegmentProductDatum.concatenate B a` is `∑ i, (a i).multisegment`.
- `concatenate_hasSegmentHeads`: segment heads survive concatenation.
