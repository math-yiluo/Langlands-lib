# Monomorphisms of actual finite split tori

Worker 1274. This internal derivation uses the published character
lattices and the actual algebra-valued points of split tori.

`characterMap` transports pullback along a group-scheme homomorphism to the
finite integral coordinate lattices. If the underlying scheme map is a
monomorphism, form the additive cokernel of this character map and test the
original map on the group algebra of that cokernel. The source point with
coordinate monomials maps to the identity, because its character exponents lie
in the killed image. Scheme-theoretic injectivity forces it to be the identity.
Linear independence of group-algebra monomials kills each coordinate generator
of the cokernel. Hence the character map is surjective.

No rank equality or conjugacy is assumed in this character-surjectivity result.
The construction is internal and uses no independent literature assertion.

For equal finite ranks, reindex the two coordinate modules to produce an
injective integral linear map between them. The published Noetherian module
lemma makes the already surjective character map injective as well. Choose
preimages of the source coordinate characters and sum their composites with
the coordinate cocharacters to construct an inverse torus morphism. The
coordinate decomposition of the identity gives one inverse equation;
injectivity of character pullback gives the other. Thus
`isIso_of_mono_of_card_eq` proves actual scheme-theoretic rigidity, without
replacing monomorphisms by injectivity merely on field-valued points.

The monomial-unit helper specializes the existing
`Diagonalizable.monomialUnits` to the field `k`.
