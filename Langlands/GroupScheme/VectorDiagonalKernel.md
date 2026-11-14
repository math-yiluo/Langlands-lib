# Diagonal vector maps and their scheme kernels

This internal construction generalizes the scalar transition calculation to a
different coefficient in each coordinate. For every commutative ring and finite
dimension, `VectorGroup.diagonal` is the group-scheme endomorphism whose value on
every scheme test multiplies coordinate `j` by the image of coefficient `c j`.
The maps compose by coordinatewise multiplication. A constant coefficient
recovers the existing scalar map, and unit coefficients give a group-scheme
isomorphism. The existing polynomial vector-group base-change isomorphism
intertwines diagonal maps using the actual coefficient homomorphism.

Over a field, a nonzero coefficient maps to a unit in the ring of global
sections of every test scheme, including nonreduced tests. The equation that
the diagonal map kills a point therefore forces precisely its nonzero-coefficient
coordinates to vanish. Conversely those equations kill the point. This proves
equality of the full image functor of the actual kernel inclusion with the
coordinate subgroup supported on the zero coefficients.

The published coordinate-block inclusion represents that subgroup. Uniqueness
of representatives then gives `diagonalKernelIso`, an isomorphism from the
actual pullback kernel to the polynomial vector group whose dimension is the
number of zero coefficients. The isomorphism commutes with the inclusion into
the original vector group. Transport of the published vector-group smoothness,
connectedness and representation-theoretic unipotence proves the three kernel
properties. The commuting base-change square gives the same properties after
any ring-to-field specialization. Zero dimension and mixtures of zero and
nonzero coefficients are included.

This is derived infrastructure for Task 6392. It extends the uniform scalar
calculation used for the additive models in Kaletha–Prasad, *Bruhat–Tits theory:
a new approach* (2023), Section C.2 and Fact C.2.1, printed pp.697–698 / PDF
pp.728–729, registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
The coordinate-block argument is an internal derivation, rather than a
separately numbered assertion of that source. Independent scales can support
lattices with unequal coordinate jumps. This pair does not identify a ramified
root lattice, construct restriction-of-scalars comparisons, or match a supplied
apartment filtration.
