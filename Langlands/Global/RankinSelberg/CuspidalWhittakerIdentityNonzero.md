# Nonvanishing of the cuspidal Whittaker functional at the identity

For an actual cuspidal realization over a number field with compact additive
adelic quotient, the standard Whittaker coefficient at the adelic identity
is nonzero on some realized vector. The rank index ranges over all natural
numbers, representing general linear groups of positive rank.

The proof is an internal consequence of the Library's cuspidal Whittaker
expansion and archimedean regularity. The expansion gives a nonzero value at
some adelic point for any nonzero realized vector, as in
`SelfPair.exists_cuspWhittaker_ne_zero`. At finite coordinate one, restriction
to the archimedean group is a smooth linear coefficient map. Differentiating
the existing archimedean Whittaker extension gives covariance for the real Lie
generators, hence for the enveloping algebra. Compact covariance follows from
the realized right action.

The center ideal annihilating a realized vector and the finite span of its
compact orbit transfer through this map. Joint-finite analyticity therefore
applies. If the identity functional vanishes, every enveloping derivative
of every coefficient vanishes at each standard compact element. Each connected
component of the archimedean group meets the compact subgroup, so analytic
jet uniqueness forces every such coefficient to vanish on the archimedean
group. Finite right translation then gives vanishing at every adelic point,
contradicting the expansion.
