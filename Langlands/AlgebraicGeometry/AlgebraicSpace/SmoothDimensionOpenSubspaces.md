# Open subspaces selected by actual relative dimension

Author: Worker 109. This derived supporting construction turns the finite
locally constant relative dimension on actual algebraic-space target points
into actual representable open subspaces. Its inputs are the published
point quotient, scheme open immersions, relative representability and open
subsheaf constructions, together with `SmoothRelativePointDimension`.

For an arbitrary subset of presheaf points, `PointOpenSubspace.subfunctor`
consists of those sections whose entire ordinary scheme-point image lies in
the subset. Naturality of the chart point maps proves the subfunctor law.
For an algebraic space and an open subset of its point space, the inverse
image in every scheme test is an actual scheme open, because arbitrary
scheme test point maps are continuous. The scheme factorization criterion
for open immersions identifies the represented open's functor with the
preimage subfunctor. The resulting pullback squares prove that its inclusion
is a representable open immersion.

The image of its quotient point map is exactly the selected subset.
One direction evaluates a section over a field at that field spectrum's
unique point. In the other direction, represent a point by a field and
section; the field spectrum is a singleton, so that section belongs to
the subfunctor whenever the represented point belongs to the selected
subset. The construction commutes with preimages of presheaf maps.
`PointOpenSubspace.space` uses the existing open subsheaf construction
to obtain the actual algebraic space.

For `SmoothTargetPointDimensions`, each dimension fibre is both open and
closed. `targetSpace` and `targetInclusion` construct its actual open
target subspace and inclusion, with the exact point image proved.
The dimensions which occur form the finite type `Index`.
The resulting finite family covers all target points, and distinct
dimension fibres have disjoint point images.

Restriction of the source morphism, fixed chart smooth dimension,
quasi-compact finite-presentation restrictions, uniform Lang-Weil and
the final adelic openness theorem are subsequent obligations.
