# Haar character of an involutive continuous automorphism

`Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.mulEquivHaarChar_eq_one_of_involutive`
says that an involutive continuous automorphism of a locally compact topological
group, equipped with its Borel measurable structure, has Haar character one.

The existing declaration and proof have been moved unchanged from
`Representation/RankinSelberg/TwoBlockFirstBlockLaurentInvolution` so that local
and global Rankin–Selberg arguments can share the result without importing each
other. Its namespace is retained for existing consumers.

The proof applies multiplicativity to the square of the automorphism. The
nonnegative real Haar character has square one and hence equals one.
