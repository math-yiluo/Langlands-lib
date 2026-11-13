# The lattice index of a simply connected orthogonal cover

Let `l` be a finite index type with at least three elements, and let `k` be any field.
Let `p : S → O(2l)⁰` be a central isogeny from a simply connected group. Suppose a split
maximal torus `i : T → S` and a torus map `t : T → 𝔻` form a commuting square with the
standard split maximal torus `OrthogonalMatrix.identityTorus l k` of the target.

`map_range_cocharacterMapInt_eq_pairLattice` states that the image of the actual integral
cocharacter pushforward, mapped through `GeneralLinear.cocharacterCoordEquiv`, is
`TypeDParityLattice.pairLattice l`. By the parity lattice calculation, these are exactly
the integer coordinate vectors whose coordinate sum is even.
`range_cocharacterCoord_eq_pairLattice` states the same formula as the range of the
composite linear map.

`centralCoverQuotientEquiv` constructs an integer linear equivalence from the target
cocharacter lattice modulo the actual pushforward image to `ZMod 2`.
`card_centralCoverQuotient` therefore gives index exactly two. All assertions hold in
arbitrary characteristic, without hypotheses on reduced kernel points.

This is an internal specialization of the general central-cover coroot-image comparison
and the explicit split orthogonal coroot calculation. The rank bound supplies a
nontrivial index type; the published reductivity of the target and root datum existence
supply a root datum of its standard torus. The general theorem
`IsCentralIsogeny.range_cocharacterMapInt_eq_corootSpan` identifies the image with its
coroot span. `map_corootSpan_eq_pairLattice` then identifies the image in coordinates.
The quotient construction transports through that coordinate equivalence and applies
`TypeDParityLattice.quotientEquiv`; cardinality follows by transport to `ZMod 2`.

The compatible split maximal torus and commuting restriction are explicit hypotheses.
This unit does not construct them for a quaternionic spin cover and does not identify
its binary Levi diagonal with its kernel.
