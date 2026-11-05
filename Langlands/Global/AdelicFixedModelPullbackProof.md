# Pullbacks of full-adele fixed-model point spaces

The theorem `Langlands.Global.adelicFixedModelPullback` proves exactly
`Langlands.Global.AdelicFixedModelPullbackStatement`. For finite-type models
`X`, `Y` and `Z` over the original ring of outside-`S` integers, with `Z`
separated, the canonical comparison on points of every limiting pullback
cone is a homeomorphism. Its target is the subspace of the product consisting
of pairs with equal images in `Z`. The factors and source have the existing
final arithmetic point topologies.

The two clauses retain arbitrary common universe `u`. The function-field
clause allows arbitrary constant fields and possibly inseparable
function-field extensions; the number-field clause uses the full adele ring,
including all infinite completions. Both allow the empty initial finite set.
The factors need not be separated or affine. No compactness or finiteness of
residue fields is used.

## Implemented proof

The private helper `continuous_of_open_covering_maps` tests continuity along
a jointly surjective family of open maps. It writes the preimage of an open
set as the union of the open images of its preimages along that family.

The private helper `isHomeomorph_pullback_transport` transports a pullback
comparison along a natural family of point homeomorphisms. The product of
the two homeomorphisms restricts to the compatible-pair subspaces because
naturality and injectivity of the base homeomorphism reflect the equality
condition. The transported comparison agrees with the actual cone-leg map.

For each arithmetic stage `T`, the two private arithmetic stage helpers use
the actual scalar inclusion from the initial integer ring to the outside-`T`
integer ring. Pullback along its spectrum map preserves the limiting cone.
The existing `adelicLevelModelPullback` theorem proves the comparison for
the base-changed models, with their original level topologies. The existing
fixed-model point homeomorphisms and `ringPointBaseChangeEquiv_natural`
transport this result back to the original scalar base. This step needs no
finite-type or separatedness assumption.

The private helper `isHomeomorph_finalRingPointPullback` passes from stages
to the independently defined final topology. At each stage the product map
from factor points to full-ring factor points is open. Injectivity of the
stage map for `Z` identifies the stage compatible-pair locus with the
preimage of the full compatible-pair locus. Restriction to this preimage is
therefore open. The resulting maps of compatible-pair spaces are also
continuous by the definition of the final topologies.

Each compatible pair over the full ring lifts to a common stage: lift its
two coordinates individually, take a filtered common upper bound, and use
cocone naturality and injectivity for `Z` to reflect their compatibility.
Consequently the restricted open maps jointly cover the compatible-pair
space. The point bijection comes from the categorical limiting cone.
Forward continuity follows by testing on every source stage. Inverse
continuity is tested along the covering open maps; on each such map it is
the stage pullback homeomorphism followed by the continuous source stage
inclusion.

Finally, in each arithmetic case `adelicFixedModelColimitOpen` supplies the
open maps for `X` and `Y` and the injective stage maps for the separated
model `Z`. `adelicFixedModelFiniteType` supplies the individual point lifts.
The final helper applies to the actual coefficient diagram and full-adele
cocone, giving exactly the existing arithmetic final topologies.

## Provenance and scope

This is a derived fixed-model extension of the discussion in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp.8–9, after Theorem 3.6 and at the beginning of Section 4.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proof follows the explicit open-stage argument above. The enlarged
scope for nonseparated factors is derived, not attributed verbatim to the
paper. Generic-fiber comparisons and the remaining whole-paper obligations
are separate results.

The target and prerequisite results are imported from the published Library.
This submission contains only the new proof pair. Worker 208 developed the
proof and its explanation; Worker 1592 checked and prepared the submission.
