# Universal closedness tested on a surjective etale target atlas

This internal unit proves the target-atlas criterion for the published
`IsUniversallyClosedMorphism` predicate, with arbitrary base scheme and arbitrary
algebraic-space morphism. It uses actual presheaf pullbacks and their specified
point topologies; the original morphism need not be represented by schemes.

The three preliminary `Points` lemmas concern arbitrary presheaves.
`exists_pullback_point` lifts any pair of quotient points whose images agree to
a point of the presheaf pullback. Representatives of the two points give maps
from field spectra. Equality of their quotient images is the published
`SameImage₂` common-test relation, which supplies a test scheme, a point and
compatible maps. The universal property of the actual presheaf pullback gives
the lift. `exists_point_of_isPullback` transports this fact to any cartesian
square. Consequently `preimage_image_of_isPullback` identifies the inverse image
of an image with the image of the inverse image on quotient point sets. No
claim that the point topology itself preserves categorical pullbacks is needed.

`targetCoverFibreMap` compares the test fibre of a target pullback with the
original test fibre when the target test lifts to a cartesian test square.
Its defining morphism preserves both projections. Pullback pasting and
cancellation prove that this comparison is cartesian over the test cover.

`IsUniversallyClosedMorphism.of_isPullback` establishes preservation in an
actual cartesian square of algebraic spaces. Each test of the new target gives
a direct test of the old target; the canonical iterated-fibre isomorphism
preserves the projection to the scheme test. The existing point-topology
isomorphism transport therefore transfers closedness.

`isUniversallyClosedMorphism_iff_targetAtlas` states the criterion for a
surjective etale map from a scheme to the target. Preservation gives one
direction. For the converse, pull this atlas back over an arbitrary test of
the target. Its represented projection is an etale surjective scheme map and
induces a quotient map onto the represented test's point space. For a closed
set in the original fibre, its inverse image in the lifted fibre is closed:
the fibre comparison is continuous, using an actual etale atlas of its target
fibre-product space. Universal closedness over the atlas gives a closed image
upstairs. The point-lifting image identity identifies this with the inverse
image of the original image. The quotient-map criterion detects that the
original image is closed, as required.

The provenance is internal: the published chart-point/common-test comparison,
actual fibre products, represented atlas projections, point-map continuity,
etale atlas quotient topology, and canonical iterated pullback isomorphisms.
The result supplies the target-local topological step of the host properness
argument. Scheme-cover existence, actual rebase comparisons, descent of the
cover and its map, and the full eight-property limit theorem remain separate
obligations.
