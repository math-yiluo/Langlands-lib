# Coordinate fibers and polysimplicial factors

This internal helper studies a bijection between product vertex sets and
a supplied bijection `σ` of their index types.
`RespectsCoordinateFibers σ e` means that output coordinate `σ i`
depends only on input coordinate `i`.

Fixing a base vertex, `coordinateMap` varies only one input coordinate.
The fiber condition proves that its value on `x i` is `e x (σ i)`,
independent of all other coordinates. Each coordinate map is bijective.
For injectivity, two updated base vertices with equal images in that
coordinate have equal images in every other coordinate by the fiber
condition; injectivity of `e` then recovers the changed input values.
For surjectivity, take the inverse under `e` of a target vertex with
the required output coordinate.

`coordinateEquiv` packages these bijections.
`piCongr_coordinateEquiv` recovers the original product equivalence.
The two projection lemmas express the coordinate projection of an image
or preimage through the associated coordinate equivalence.
The index universes agree, as required by the existing
`AbstractBuilding.PolysimplicialIso` interface; the two vertex universes
are independent.

Now let `K` and `L` be the existing finite-product polysimplicial complexes
on these vertex families. Suppose that `e` sends every facet of `K`
to a facet of `L`, and that its preimage sends every facet of `L`
to a facet of `K`. The lemmas `coordinateEquiv_image_mem` and
`coordinateEquiv_preimage_mem` prove preservation of factor simplices.
For the image direction, put a given factor simplex in coordinate `i`
and the singleton of the base vertex in every other coordinate.
This product is a facet of `K`; project its image facet to `σ i`.
The projection is a face of that factor of `L`, and the projection
identity identifies it with the image of the original simplex.
For the preimage direction, use a product facet of `L` with the
given simplex at `σ i` and singletons of `e a` elsewhere, then
project its preimage facet to `i`.

`toPolysimplicialIso` packages `σ` and these simplicial isomorphisms
as a `PolysimplicialIso K L`. Its induced vertex equivalence is exactly
`e`, by `toPolysimplicialIso_vertexEquiv`.
Conversely, `PolysimplicialIso.respectsCoordinateFibers` follows
from the formula for its induced vertex map.
Thus `exists_polysimplicialIso_iff_respectsCoordinateFibers` proves,
under the two supplied facet-preservation assumptions, that `e`
comes from a polysimplicial isomorphism if and only if there is an
index bijection `σ` for which `RespectsCoordinateFibers σ e` holds.
The reverse implication chooses a base vertex from the nonempty
vertex sets of the factors.
`isPolysimplicialAutomorphism_iff_respectsCoordinateFibers` is the
specialization to automorphisms of one complex, under the same
two facet-preservation assumptions.

This is an internal deduction from the actual product-facet and
isomorphism definitions in `AbstractBuilding`, using elementary
properties of product projections and bijections. No external assertion
is introduced. Existence of an index permutation satisfying the fiber
condition for an actual building action remains a geometric obligation;
this unit supplies no actual building data or realization.
