# Homogeneous quotients from coordinate-line stabilizers

This internal construction connects the existing actual relative projective
coordinate section and matrix orbit map to the smooth-relation quotient
construction. It retains every relative scheme test, including nonaffine
and nonreduced schemes.

`pullbackPoint_basisSection` identifies the normalized pullback of the
coordinate section with the same coordinate section on the new base, for
every scheme morphism. The proof compares the base and integral projective
projections. The base projection is the identity, and the integral projection
agrees by naturality of the coordinate section.

`basisSection_matrixAction_eq_iff` says that an invertible matrix over the
global functions of any scheme fixes its actual coordinate section exactly
when it sends the coordinate vector to a multiple by one global unit. This
is the existing relative global-linear-action criterion, using
`coordinateEquiv_apply` to identify the coordinate action with matrix-vector
multiplication.

Suppose an actual matrix representation of `G` on `Fin (n+1)` and an index
`j` have the following property: on every relative scheme `T`, membership
in `SubgroupFunctor.range i` is equivalent to multiplying `e_j` by some
unit of the ring of global sections of `T`. Then
`basisSection_orbitMap_fibers` identifies equality of the actual projective
orbit images of `g` and `h` with membership of `g⁻¹ h` in that range.
The existing orbit-fiber theorem reduces equality to fixing the pulled-back
coordinate section; the two preceding lemmas and the assumed stabilizer
criterion finish the comparison. No test schemes are discarded.

Over any field in universe `u`, assume `G` has smooth affine structural
morphism, `i : H → G` is a closed subgroup, and `H` is smooth over the
field. Given the representation and its all-test criterion just described,
`quotientOfLineStabilizer` chooses an actual homogeneous quotient using
`HomogeneousQuotientFromEmbedding.quotientOfMapKernel`. The ambient is the
existing separated relative projective scheme, and the map is the actual
orbit morphism of the coordinate section. The resulting structure contains
a separated, locally finite-type, quasi-compact scheme over the field, a
smooth, surjective, quasi-compact projection from `G`, and exact right-coset
fibers on every relative scheme test.

The provenance is the composition of the imported constructions and proved
identities. This module assumes the line-stabilizer representation as input;
it does not assert its existence. It adds no connectedness, reductivity,
characteristic or field-cardinality hypothesis.
