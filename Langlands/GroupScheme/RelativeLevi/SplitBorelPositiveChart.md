# Positive-root chart data for the actual contracting group

`SplitBorelPositiveChart i P` packages a regular integral cocharacter for
the actual coordinate torus `i`, the actual affine contracting group of
that cocharacter, an ordered family of additive root homomorphisms into
that group, positive natural heights, and an isomorphism of its underlying
scheme with coordinate affine space. The isomorphism has the ordered
root-product formula on every test scheme. The point subgroups of the
root maps satisfy the standard commutator bound at the sum of their
heights on every test scheme. The source chart asserts an isomorphism of
schemes over the base; the contracting group need not have the additive
group law.

`nonempty_splitBorelPositiveChart` constructs such data from a reductive
group with a fibrewise maximal coordinate split torus, its actual common
fibrewise root datum, and supplied actual root parametrizations of all
roots. It works over an arbitrary commutative ring, including the zero
ring, and in every universe. In particular, it requires no Borel or
kernel series as input.

The proof uses finiteness and reducedness from the fibrewise root datum
to choose a base. The integral cocharacter supplied by
`LocalSplitCell.exists_cocharacter_of_base` pairs positively with the
positive roots and negatively with all other roots, hence is regular.
Finite equivalences enumerate the two root subsets. The supplied actual
root parametrizations give torus equivariance and the arbitrary-ring
open big cell through `LocalSplitBigCell.isOpenImmersion_cellMap`.
`SplitBorelPositiveIso` constructs the positive-product scheme
isomorphism onto the actual contracting representative.
`SplitBorelPositiveFactors` gives its internal product formula, and
`SplitBorelUnipotentCommutator` gives its internal commutator bound.
Taking natural parts of the positive cocharacter pairings provides the
positive natural heights.

This is a derived assembly of the indicated Library constructions.
Conrad, *Reductive group schemes* (2014), Theorem 5.1.13, pp.143–145,
motivates the actual positive-product chart, and Proposition 5.1.16,
pp.146–148, motivates the height filtration. The package supplies the
input to the separate construction of represented vector quotients.
It does not construct the supplied global root parametrizations or the
finite affine vector series, so it does not yet prove
`SplitBorelVectorSeriesStatement`.
