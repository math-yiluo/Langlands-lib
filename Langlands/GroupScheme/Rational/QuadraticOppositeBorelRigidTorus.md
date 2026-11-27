# Splitting and anisotropy of a quadratic opposite-Borel torus

`IsQuadraticOppositeBorelTorus.split_anisotropic` takes a semisimple
group with actual Tits index data, a quadratic opposite-Borel torus,
and rigidity of the Cartan matrix on the simple vertices. The torus
splits over the given quadratic extension and has split rank zero
over the base field.

The proof extends the regular cocharacter of the Borel pair to the
separable closure and chooses its positive base. The dynamic
unipotent subgroup stays fixed under automorphisms fixing the
quadratic field and becomes the opposite subgroup under
automorphisms inducing the nonidentity automorphism. The comparison
of positive root supports then makes the ordinary action preserve
the base in the first case and makes its product with simultaneous
negation preserve the base in the second case.

Conjugacy of split pinnings identifies the Cartan integers of the
chosen base with those of the supplied Tits index. A based
automorphism preserves the Cartan integers and therefore fixes every
simple index. The simple roots span the root lattice, and the root
lattice has finite index in the torsion-free character lattice by
semisimplicity. The based automorphism acts as the identity on the
whole root datum. This computes the character action as the identity
above the quadratic field and as negation above its nonidentity
automorphism.

For splitting, restrict the action to the absolute Galois group of
the quadratic field using the tower isomorphism. At a finite Galois
splitting field of the extended torus, lift its automorphisms to the
algebraic closure and descend a split-torus isomorphism using the
fixed characters. For anisotropy, a ground-field cocharacter pairs
with a character by an integer invariant under Galois transport.
An automorphism above the nonidentity automorphism negates the
character and fixes the cocharacter, so that integer is zero.
Perfectness of the lattice pairing and injectivity under base change
force the original cocharacter to vanish.

The sign argument uses the opposition computation of Platonov and
Rapinchuk, *Algebraic Groups and Number Theory* (1994), Lemma 6.18,
printed p. 330, with rigidity of the full Cartan matrix resolving the
permutation of simple roots.
