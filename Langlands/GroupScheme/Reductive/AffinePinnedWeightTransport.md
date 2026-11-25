# Actual exponent-weight transport for affine pinned comparisons

This internal module transports the actual all-test exponent weight spaces along a compatible group isomorphism and a coordinate torus isomorphism with the corresponding monomial identity. It works over every commutative ring. The induced linear equivalence has the actual target Lie map as its underlying map.

The proof evaluates the source weight equation at the inverse image of an arbitrary target torus point, applies naturality of the actual Lie map with respect to coefficient extension and adjoint action, and uses the prescribed character identity. The inverse map uses the inverse square and the same identity. Monomial identities on arbitrary test schemes specialize to affine test algebras through the global-section/spectrum unit comparison.

The provenance is an internal exponent-coordinate analogue of the Library's character-weight transport in `Rational.CrossTorusLieTransport`. It supports the transport of root-line generators in Conrad, *Reductive group schemes* (2014), the proof of the pinned Isomorphism Theorem, Theorem 6.1.17, p.197, using Proposition 6.1.13 and Corollary 6.1.15, pp.194–196.
