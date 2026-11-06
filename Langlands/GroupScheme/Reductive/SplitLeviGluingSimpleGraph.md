# The actual graph and its paired simple-root families

Authors: Worker 1444, with the graph-root construction of Worker 712.

Work over an arbitrary field `k`, with smooth affine group schemes `G₁` and
`G₂` over `Spec k`, a commutative group scheme `T`, and homomorphisms
`i₁ : T.toGrp ⟶ G₁` and `i₂ : T.toGrp ⟶ G₂`.
The record `SimpleComparisonGraph` contains a proof that `T` is split, a
`SimpleRootDirections i₁` family, one local Levi comparison for each of its
simple-root kernel directions, and their actual generated graph envelope.
For its constructor `simpleComparisonGraph`, also assume that `G₁` is connected
and that the exact local rank-one Levi hypothesis holds. The existing
constructors then supply all those objects. No chamber, root-group family,
local representative or graph is another input of this constructor.

For a given constructed graph, `positiveRoot` and `negativeRoot` choose the
intrinsic root representatives for the simple character and its negative in
the same local Levi comparison. The actual maps `positiveHom` and `negativeHom`
are their graph lifts. Their sources are smooth connected affine groups and
the maps are closed subgroup inclusions. Their composites with either graph
projection represent the corresponding full intrinsic root functors of the
two ambient groups on every scheme test. The negative-character zero pairing
follows by negating the simple-character zero pairing.

Both root ranges are normalized by the graph's distinguished torus on every
test, using the represented root actions. Positivity of a simple character
places the positive range in the actual dynamic unipotent subgroup of the
chosen graph cocharacter. Pairing both the negative character and negative
cocharacter gives the same positive integer, so the negative range lies in the
opposite dynamic unipotent subgroup. These conclusions are containments;
equality with the dynamic factors is not asserted.

For `commute_positive_negative`, further supply root data realizing each
ambient root set and equality of those root sets. The common chamber is then
generic for both, and their intrinsic simple-root sets agree. For distinct
simple indices, the preceding all-test ambient commutation theorem applies to
the first projection and to the second projection. The ambient representation
equations place the projected points in those exact intrinsic root functors.
The graph envelope's joint injectivity on all tests turns the two commuting
projection equations into commutation inside the graph. Neither projection
is assumed individually injective or invertible.

The provenance is internal composition of the existing simple-root directions,
local Levi comparisons, graph-root lifts, dynamic containment and ambient
commutation results. The root-set equality in the last theorem is a retained
helper hypothesis to be discharged from the root reindexing in the main target.
The module proves no algebraic generation by simple-root groups, graph density,
equality of dynamic factors or global projection invertibility, and does not
prove the main isomorphism or Levi gluing proposition.
