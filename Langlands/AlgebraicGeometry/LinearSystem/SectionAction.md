# Coordinate action from an actual finite section basis

This internal derived construction uses an actual scheme isomorphism over a
field, an actual isomorphism from the pulled-back line bundle to itself, and a
finite ordered basis of all global sections over that field. It constructs the
induced linear equivalence on sections and its dual coordinate equivalence.
Generation at every scheme point yields equivariance of the actual projective
linear-system morphism. The section basis, bundle isomorphism and generation
are inputs; this file does not prove their existence or moduli representability.

The section map is actual pullback followed by the specified sheaf isomorphism.
Base preservation proves linearity over the field. The existing zero-reflection
lemma for scheme isomorphisms and invertibility of the sheaf isomorphism give
injectivity. The finite basis gives finite dimension, so the injective map is
an equivalence. Conjugating its dual by the dual-basis coordinate equivalence
produces the coefficient convention of `linearChangeSections`: entry `(i,j)`
is coefficient `j` of the transported basis section `i`. The basis expansion
proves equality of transported sections and this coordinate change. Applying
`linearSystemMap_equivariant` proves equality of actual scheme morphisms.
No new external source assertion is used.
