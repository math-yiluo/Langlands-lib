# Actual Levi-compatible Iwasawa for reductive dynamic pairs

Author: Worker 1655.

This internal construction combines the published adjoint-stable
realization theorem with the published arbitrary-`RCLike` internal
cocharacter conjugation and polar construction. For every `RCLike`
field `k : Type u`, connected reductive group scheme `G` over `Spec k`,
and cocharacter `χ`, let the actual maps `p : P → G` and `m : M → G`
represent its dynamic parabolic and dynamic centralizer on all test
schemes. The construction produces a compact subgroup with all four
Levi-compatible Iwasawa conclusions on the original actual point groups.
The universe `u` is arbitrary.

`IsConnectedReductive.hasClosedStarRealization` applies
`SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement`
to `k`, `G` and its reductivity proof. Thus the closed ambient matrix
representation and adjoint stability of its full rational-point image
are constructed by a published theorem. They are not inputs here.
`hasHermitianStarLeviRealization` then applies the published real/complex
internal conjugation construction to the supplied common cocharacter.
Its representation may change, while the represented maps `p` and `m`
remain fixed. Unitary diagonalization gives
`hasDiagonalStarLeviRealization`.

`IsConnectedReductive.hasLeviCompatibleDecomposition` obtains ambient
affineness from reductivity and applies the existing diagonal polar
construction. The topology on every point group is exactly the
regular-function evaluation topology `affinePointsTopologicalSpace`.
The conclusion is the existing `HasLeviCompatibleDecomposition`, for
the actual homomorphisms `P.affinePointsTarget p` and
`M.affinePointsTarget m`. It gives ambient compactness and maximality,
coverage by the parabolic image times the compact in that order,
equality of the parabolic and specified Levi intersections with the
compact, and compactness and maximality of the inverse image in the
original Levi point group with its own evaluation topology.

`Dynamic.reductiveLeviIwasawaCompact` chooses the subgroup from this
existence theorem. `reductiveLeviIwasawaCompact_spec` is its choice
specification, so the same selected subgroup has all four properties.
No uniqueness is asserted.

The provenance is internal composition of the published ambient
realization, internal cocharacter conjugation, Hermitian diagonalization
and polar Iwasawa theorems. No supplied realization, compact subgroup,
decomposition or topology comparison is a premise. Existence of a
common cocharacter for an arbitrary supplied rational parabolic and
Levi remains a separate obligation. This module proves the dynamic-pair
case and does not assert the unconditional archimedean host proposition.
