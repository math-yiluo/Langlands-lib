# A finite family as a multiset sum

`Langlands.Classification.SegmentProductCuspidalEmbedding.ofFn_multiset_eq_sum`
identifies the multiset of `List.ofFn f`, for any family `f : Fin k → α`, with
the sum of its singleton multisets. The assertion includes the empty family.
Its proof rewrites Mathlib's sum-of-singletons identity using `List.map_ofFn`
and `List.sum_ofFn`.

The declaration, its public name and its proof are relocated unchanged from
[SegmentProductCuspidalMembers](../Representation/Classification/SegmentProductCuspidalMembers.md).
This general algebra module lets the segment-member and binary cuspidal-family
constructions reuse one declaration without a new classification dependency.
No mathematical result is added by the relocation.
