# Smooth group actions on represented unipotent radicals

Worker 1372. Internal construction using published radical maximality, actual
radical quotient existence, and determination of morphisms by rational points.

`AutomorphicAction.sectionIso` turns a section of the acting group over an
arbitrary scheme base into an actual target group-scheme automorphism. Its point
formula is obtained from the natural point automorphisms and the published
`isoOfPoints` construction.

Over an algebraically closed field, let a smooth group scheme H act by
scheme-theoretic automorphisms on a smooth connected affine group scheme G.
For any supplied unipotent radical representative i : U ⟶ G,
`IsUnipotentRadical.isStable` asserts stability of its full range on every test
scheme. The proof chooses an actual affine radical quotient q : G ⟶ Q with the
full radical kernel. The product H × U is smooth, hence reduced and locally of
finite type. Its action morphism followed by q is equal to the identity section:
at every rational pair, the section-induced ambient automorphism carries i to
another greatest radical, so uniqueness of the radical range makes the composite
trivial. The separated target and rational-point determination give an equality
of morphisms. Precomposition then proves stability on every test scheme,
including nonreduced tests, by the full kernel equality.

`IsUnipotentRadical.action` constructs the induced automorphic action on U using
its closed representing inclusion and the proved stability. The grouped
`action_isEquivariant` lemma gives the inclusion equation for every test scheme.
No smoothness, connectedness or affineness of a test scheme is required. The
acting group is assumed smooth, but need not be connected or affine. The result
retains algebraic closedness of the field, ambient smoothness, connectedness and
affineness, and a supplied radical representative.

This is a derived internal result, not a new literature assertion. It discharges
radical stability for smooth torus actions in the normal semigroup reduction;
it does not prove radical intersection, reductivity of the quotient, or the
remaining semigroup comparison prerequisites.
