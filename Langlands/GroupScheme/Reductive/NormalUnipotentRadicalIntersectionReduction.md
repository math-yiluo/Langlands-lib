# Radical intersection from a torus containing the full centre

Worker 1372. Internal conditional construction using normal unipotent
commutation, closed split-torus/unipotent intersection, actual radical
quotients, quotient subgroup descent and schematic homomorphism images.

The module constructs `normalUnipotentIntersectionTrivialIso`, an actual
isomorphism from the scheme-theoretic intersection of a smooth connected
normal unipotent subgroup and a connected reductive normal subgroup to
the trivial group scheme. Its additional input is a supplied closed split
torus in the reductive subgroup containing its full centre. The previously
proved commutation theorem puts the intersection in the centre. Every
test point therefore factors through the split torus and through the
unipotent subgroup with the same ambient image. The published closed
split-torus/unipotent intersection theorem forces it to be the identity.
Represented-subgroup uniqueness constructs the actual isomorphism.

Over an algebraically closed field the trivial-action specialization of
`FixedCenterContainingTorusStatement` supplies this torus. The module
then derives `NormalUnipotentRadicalIntersectionStatement` from that
existing structural premise.

For a closed normal inclusion `H ⟶ G` and supplied radicals `V` and `U`,
the radical of `H` is normal in `G` by the published ambient radical
normality theorem. Quotient `G` by this actual subgroup `V`, and quotient
`H` by its radical. Exact kernel cancellation gives a closed normal
inclusion of `H/V` into `G/V`. The former is connected reductive over the
algebraically closed field by the proved pseudo-reductive comparison.
The actual schematic image of `U ⟶ G/V` is a smooth connected normal
unipotent closed subgroup: the image theorem supplies smoothness,
connectedness and an fpqc projection, quotient-square descent supplies
normality, and unipotence descends along the flat surjection.

The preceding trivial-intersection argument applies to these two
subgroups of `G/V`. Any original test point in the inverse image of `U`
has image in this trivial intersection, hence lies in the kernel `V` of
`H ⟶ H/V`. The opposite containment is the previously proved inclusion
of normal subgroup radicals. All tests, including nonreduced tests, and
every universe are retained.

The fixed centre-containing torus proposition remains an explicit premise.
This module does not prove it or the unconditional semigroup comparison.
