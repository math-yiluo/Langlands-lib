# Coordinate refinement of the unitriangular filtration

This internal construction refines the published
`TriangularLayer.W` superdiagonal filtration by individual coordinates.
All assertions hold over an arbitrary commutative ring. No reduction,
smoothness or connectedness condition occurs.

`ZeroBefore b X` says that every row of `X` with index below `b` vanishes.
`refinedW A N a b` consists of elements of `W A N a` whose `a`-th layer
satisfies this condition. That layer is supported on the `(a + 1)`-st
superdiagonal, so each successive row imposes at most one additional
coordinate equation. The construction proves that these terms are subgroups,
decrease with the row bound, start at `W a` and end at `W (a + 1)`.

The refined terms are invariant under conjugation by every upper triangular
invertible matrix and commute with every coefficient-ring homomorphism in
the sense that such a homomorphism maps each term into the corresponding
term over the new ring. The proofs use the published `layer_mul`,
`layer_inv`, `layer_conj` and `layer_map_W`.

`layerCoordinate A N a i j` is a group homomorphism from `W a` to the
multiplicative notation for the additive group of `A`. At a position
`j = i + a + 1`, it is the original matrix entry. Within the refined term
with row bound `i`, the next term is exactly its zero locus, expressed
as `layerCoordinate = 1`. This is an equality over the original ring,
including nilpotent coefficients.

The conjugation formula multiplies this coordinate by the `i`-th
diagonal entry of the inverse conjugating matrix and the `j`-th diagonal
entry of that matrix. The coordinate also commutes with every
coefficient-ring homomorphism.

These are matrix subgroup and coordinate constructions. The module does
not claim representability of the refined subgroups, existence of
quotients, a group-scheme tower or a splitting section. Those remain
separate steps in the triangular diagonal splitting proof.

The provenance is internal refinement of the existing matrix filtration;
no additional literature result is assumed.
