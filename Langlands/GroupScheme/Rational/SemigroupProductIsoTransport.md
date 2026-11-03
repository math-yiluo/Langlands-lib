# Exact semigroup products under equivariant isomorphisms

This internal transport unit works at every universe over any field, with
two actual affine group schemes, actions of the same commutative group
scheme, and a supplied equivariant group-scheme isomorphism `e`. It does
not require the acting group to be split, nor the two affine groups to be
smooth, connected, solvable or unipotent.

`actionWeightSupport_eq_of_equivariant_iso` identifies the entire intrinsic
Lie support. The proof applies the existing support transport under
equivariant monomorphisms to the full subgroup. Every point of the target
lifts by the inverse of `e`, so the range of its forward map is the full
subgroup. An occurring zero character is retained.

`semigroupSubgroup_map_equivariant_iso` identifies the exact all-test image
of each existing semigroup subgroup with the subgroup for the target
action. It applies the existing closed-inclusion comparison: an
isomorphism is closed, and the required containment in its range holds for
every subgroup. This uses no assumed global functoriality or intersection
statement, and applies to arbitrary additive subsemigroups, including the
empty one.

`semigroupPointsEquivOfIso` constructs the canonical multiplicative
equivalence between these semigroup points on every scheme over the
original field. It specializes the existing
`semigroupSubgroupPointsEquiv` using the full range of the isomorphism.
Its forward map is precisely postcomposition with `e.hom`, as recorded
by `semigroupPointsEquivOfIso_val`.

`HasOrderedSemigroupProducts.map_equivariant_iso` transfers the exact
ordered-product property for one action. Given a partition of the target
support, support equality makes the same partition admissible for the
source. The same representative groups, with their maps composed with
`e.hom`, represent exactly the target semigroup subgroups. Closedness,
smoothness and connectedness of these representatives follow from their
original properties and composition with the isomorphism. The existing
`orderedMultiplication_comp` identifies the new ordered product with the
original ordered product followed by `e.hom`; hence it is an isomorphism.
Applying this construction to the inverse equivariant isomorphism gives
`hasOrderedSemigroupProducts_iff_of_equivariant_iso`.

The blocks, their positive additive closures, the exact cross-exclusion
hypothesis, arbitrary orderings, and the case of zero factors are
unchanged. These are derived constructions from the imported actual
support, closed-inclusion and ordered-product interfaces. This unit
constructs neither a solvable-group decomposition nor scalar descent,
and does not prove the full `SemigroupOrderedProductStatement`.
