# Weighted intertwining expansions for standard wave packets

`StandardWeightedIntertwiningExpansionsStatement` specializes the finite
expansion premise `IntertwiningSquareIntegrableExpansionStatement` to the
weighted inducing vectors of a standard wave packet. It uses the supplied
comparison between regularity for the source root presentation and regularity
for the standard parabolic. The expansion length and the domain of holomorphy
are common to all standard target parabolics and Weyl indices. The domain
contains the entire imaginary axis of the source parabolic.

`exists_allStandardWeightedIntertwiningExpansions` first enumerates the Weyl
parameter maps into each target using `exists_weylParameterEnumeration`.
It applies the expansion premise to each representative and each fixed
inducing vector. The regularity comparison transfers the resulting thresholds
to standard coordinates. On the finite index set of triples consisting of a
target parabolic, a Weyl index and a wave-packet index, the theorem then applies
`wavePacketWeightedExpansions`. Zero belongs to each square-integrable
inducing space, so vectors and coefficients can be padded before multiplying
by the entire weights. Intersecting the coefficient domains keeps the whole
imaginary axis inside the common domain.

The fixed-vector input comes from the meromorphic intertwining families
described in Lapid (2011), §2, p. 312 (volume PDF p. 321). The weighted
expansions supply the two families entering equation (18) in §8, p. 328
(volume PDF p. 337).
