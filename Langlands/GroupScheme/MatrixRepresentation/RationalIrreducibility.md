# Actual and rational-point irreducibility

This internal derived unit compares the two irreducibility predicates on the
entire original coordinate space of a supplied finite matrix representation.
The field has arbitrary universe `u`; the additive-family index in the final
corollaries has an independent universe `v`.

For an affine ambient group, every subspace stable on all affine tests carries
a rational-point subrepresentation with exactly that underlying subspace.
Consequently rational-point irreducibility implies all-test irreducibility.
Nontriviality of the coordinate space follows from nontriviality of the
subrepresentation lattice and injectivity of its map to submodules. This
implication needs no algebraic closure, reducedness or characteristic premise.
Actual irreducibility also implies that the coordinate type is nonempty.

For a reduced affine ambient group locally of finite type over an algebraically
closed field, `rationalSubrepresentationOrderIso` identifies all-test stable
subspaces, ordered by inclusion, with subrepresentations of
`rho.rationalRepresentation`. Both directions preserve the underlying subspace
literally. The inverse uses the published
`isStableSubspace_of_rationalMatrix` theorem. The affine-test predicate still
quantifies over every affine test algebra, including nonreduced ones; reducedness
is required only of the ambient group. The two irreducibility predicates are
therefore equivalent, with nontriviality included on both sides.

In prime characteristic, suppose a supplied family of actual morphisms from
the one-dimensional vector group geometrically generates this ambient group.
For any supplied rationally irreducible first representation `rho`, there is an
exponent bound `E` such that, for every `e >= E` and every supplied rationally
irreducible second representation `sigma`, the entire rational-point
representation of `rho.tensor (sigma.frobeniusPower p e)` is irreducible. The
bound is chosen before the second coordinate type and representation. The
nonempty coordinate instances needed by the actual tensor theorem are derived
from the input irreducibility. A second corollary chooses such an exponent
above any prescribed natural number.

The proof transfers both supplied factors to all-test irreducibility, applies
`AdditiveFiniteCutoff`'s uniform eventual tensor theorem, then transfers the
result back through rational-point detection. The cofinal assertion chooses
the maximum of the eventual bound and the requested lower bound.

The provenance is the imported stability-detection results in
`Reductive.CharZeroSemisimplicity.TangentStability` (whose rational section
has no characteristic-zero hypothesis), the actual rational-point action in
`Reductive.InvariantLinearForm`, Mathlib's subrepresentation order, and the
proved finite-cutoff result. No new literature assertion is used. The unit
does not construct a generating family, Borel, torus, Steinberg representation,
induced-space comparison or big-cell decomposition, and does not prove
`SteinbergBigCellStatement`.
