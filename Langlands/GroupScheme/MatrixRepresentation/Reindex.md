# Reindexing actual matrix representations

For an actual matrix representation `rho` over an arbitrary commutative base
ring and a bijection `e : n equiv m` of finite coordinate types,
`rho.reindex e` reuses the published
`Chevalley.reindexRepresentation e R rho`. Its invertible-matrix action is
exactly the published `Chevalley.reindexGL e`, evaluating both row and column
at `e.symm`. This module constructs no second group-scheme reindexing morphism.

`reindexGL_map` records the coefficient-ring naturality of that existing
matrix action. `reindex_pointMatrix` reuses its published all-scheme-test
formula; `reindex_affineMatrix` derives the affine-algebra formula through
the canonical global-section isomorphism. `reindex_symm` proves that the
inverse coordinate bijection recovers the original actual representation,
using equality on all scheme tests. No geometric assumptions are imposed
on the group scheme.

Over a field, `reindexVector` is the coordinate linear equivalence.
`reindex_coefficient` proves that it commutes with every affine-test
translate followed by every ground-field linear functional. Therefore
`isStableSubspace_reindex_map_iff` transports the exact all-test
stable-subspace predicate along this equivalence. This retains every test
algebra, including nonreduced ones, and requires no affineness or reducedness
of the group.

`isSemisimple_reindex_iff` converts the exact semisimplicity predicate to
existence of stable complements and transports both stability and the
ambient complement equations by the induced order isomorphism of submodule
lattices. Consequently `isSemisimple_of_fin_linearlyReductive` shows that
linear reductivity formulated only for coordinate types `Fin d` controls
representations on every finite coordinate type. This applies, for example,
to the finite monomial index of symmetric powers.

This is internal infrastructure derived directly from the existing actual
matrix-representation, all-test stability and stable-complement APIs and
the published Chevalley reindexing constructor and Mathlib's submodule-map equivalence. It makes no
additional source theorem or Nagata classification claim.
