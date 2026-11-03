# Exact semigroup factors in an actual semidirect product

This internal unit works with an actual action of an affine smooth group `K`
on an affine smooth group `G` over any field and universe. A split torus `S`
acts on `G` and commutes with the `K` action. The constructed external action
on `G ⋊ K` fixes `K` on every test scheme.

The first two lemmas apply over any base scheme. If a subgroup functor of
the actual semidirect product contains the entire acting factor, its
restriction to the normal factor is stable under the inner action:
conjugation by an acting-factor point is that action. Its normal coordinate
belongs to the restriction precisely when the whole point belongs to the
original subgroup. Multiply by the inverse acting coordinate for the
forward direction and use the canonical two-factor decomposition for
the reverse direction.

For a positive additive semigroup excluding zero, the exact ambient
semigroup is the image of the normal-factor semigroup. This conclusion
assumes `SemigroupFunctorialityStatement`: the equivariant projection maps
it into the semigroup subgroup of the trivially acted-on `K`, which is
the identity. The actual kernel is the normal inclusion. The existing
closed-inclusion generator transport then identifies the image exactly.
This part does not use the intersection comparison.

For a semigroup containing zero and connected `K`, the whole acting
factor lies in the ambient semigroup, by trivial-action top and
closed-inclusion generator transport. If `G` is also connected, the source
`SemigroupIntersectionStatement` identifies its restriction to `G` with
the normal-factor semigroup. The normality hypothesis of that statement
is proved using the projection kernel, on all tests. These facts give
inner stability of the normal-factor semigroup and identify the ambient
functor with its extension by all of `K`.

`semidirectSemigroupAction` restricts the original inner action to any
given representative of that normal-factor semigroup.
`semidirectSemigroupInclusion` is its actual semidirect inclusion into
`G ⋊ K`. It represents the exact existing ambient semigroup functor and
is closed whenever the given normal inclusion is closed.

The provenance is internal, using actual semidirect point coordinates,
trivial-action weight support, and closed-inclusion generator transport.
The global functoriality and intersection statements are explicit,
unproved premises where named above. No general comparison, solvable
decomposition, scalar descent, or ordered-product target is proved here.
