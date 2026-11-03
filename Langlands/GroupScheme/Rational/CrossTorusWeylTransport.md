# Actual normalizer, centralizer and relative Weyl group transport

This internal construction identifies the actual normalizer and centralizer
base point groups under a supplied commuting square of an acting commutative
group scheme isomorphism and an ambient group scheme isomorphism. It derives
from the published definitions in `Torus.Maximal`, the naturality of inner
automorphisms in `ConjugacyBaseChange`, the lattice identification in
`Torus.LatticeGalois`, and the rational quotient and action in
`Rational.RelativeRoots` and `Rational.RelativeWeylCharacterAction`.

The construction requires actual isomorphisms `e : T ≅ T'`, `f : G ≅ H`,
and the equality `i ≫ f.hom = groupHom e.hom ≫ j`. It proves no existence
or conjugacy theorem. No splitness, maximality, reductivity, smoothness,
affineness, or finiteness hypothesis is required.

For an arbitrary base scheme, a source normalizing point `n` with
automorphism `σ` maps to the actual point `n ≫ f.hom` with transported
automorphism `e.symm ≪≫ σ ≪≫ e`. Naturality of inner automorphisms and
the supplied square give that identity. Applying the inverse square
reflects both normalizer and centralizer membership. The two multiplicative
equivalences restrict precisely the forward and inverse ambient maps.
Centralizing points refer to the identity of the whole acting group scheme,
so their definition retains every test scheme.

When the embeddings are monomorphisms on underlying schemes, their chosen
normalizing automorphisms are unique. The resulting Weyl action on the
whole character lattice therefore intertwines the identification
`characterLattice.congr e`, which precomposes characters by `e.inv`.

Over any field, the normalizer equivalence maps the centralizer subgroup
onto the target centralizer subgroup. The standard quotient congruence
constructs `relativeWeylTransportEquiv` between the actual groups `N(k)/Z(k)`.
On a normalizer representative its formula is the class of the ambient
image. Quotient induction gives the same character-action intertwining.
This construction concerns quotients of rational points, and asserts no
comparison with the rational points of a sheaf or scheme quotient.
