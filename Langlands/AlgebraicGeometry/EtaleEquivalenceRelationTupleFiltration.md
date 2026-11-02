# A finite invariant filtration from distinct related tuples

This internal helper is derived from the distinct-tuple construction in Stacks
Lemma 68.8.3, Tag 0BBN, first and second proof paragraphs. The original is
registered as `stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
The source constructs decreasing opens from images of unordered distinct tuples.
Here the opens are constructed directly on the object scheme of the relation,
by saturating images of ordered distinct tuples under the actual point
equivalence relation. The filtration calculations are derived from the
previous tuple bound and the published point-relation interface. They assume
no algebraic-space quotient or source-descent theorem.

For any étale equivalence relation `E`, `pointSaturationOpen W` is the target
image of the source preimage of an open `W`. It is open because the source is
continuous and the target is open. `mem_pointSaturationOpen` expresses membership
as being related to a point of `W`. Reflexivity proves `le_pointSaturationOpen`;
inclusion of witnesses proves monotonicity; transitivity proves invariance.
An invariant open equals its saturation, giving idempotence. Saturation
preserves the top and bottom opens. When the source is quasi-compact, it also
preserves quasi-compactness of opens: first take a compact source preimage,
then its continuous target image.

Assume the source map is separated. `tupleImageOpen n` is the image of the
zeroth coordinate on the distinct-tuple scheme with `n + 1` coordinates; this
image is open by étaleness. `tupleThresholdOpen n` is its open saturation.
These threshold opens are invariant, so their source and target preimages
agree. Selecting the first `m + 1` coordinates from an `n + 1` tuple when
`m ≤ n` proves the images decrease; monotonicity of saturation gives the same
for threshold opens. A single-coordinate tuple is automatically distinct, so
both opens at index zero are the whole object scheme.

`tupleDegreeLocus n` is the set difference of threshold opens at `n` and
`n + 1`. The declaration supplies only a set of underlying scheme points,
without a scheme structure or an identification with a geometric fiber
cardinality. It is locally closed as an open intersected with a closed
complement, invariant by symmetry and invariance of the opens, and disjoint
from the locus for every other index by the decreasing property.

When `E.U` and `E.R` are affine, the tuple-image opens are quasi-compact
because the distinct-tuple schemes are affine. Quasi-compactness of the
source then gives quasi-compact threshold opens. The previous uniform
tuple-length bound makes the distinct-tuple scheme empty for every index
at least `tupleLengthBound`, so the image and threshold opens there are
empty. Finally `exists_unique_tupleDegreeLocus` finds the least index at
which a given point leaves the threshold opens. This index is positive
and at most the bound, so the preceding index is its unique degree-locus
index and is strictly less than the bound.

All declarations allow an arbitrary universe `u`. This helper does not
identify a degree locus with an unordered tuple scheme, construct reduced
closed subschemes on those loci, prove étaleness of symmetric endpoints,
or establish the Noetherian first-level statement.
