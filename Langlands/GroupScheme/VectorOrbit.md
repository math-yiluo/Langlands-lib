# Actual affine vector actions and coordinate-vector orbit maps

This internal construction combines the published actual matrix representation,
the vector group's natural coordinates on all relative scheme tests, and the
construction of an action morphism from natural point actions. It works over
an arbitrary commutative coefficient ring and in every universe.

`VectorOrbit.pointAction` applies the coefficient matrix to the coordinates of
a vector-group point. Pullback of global functions commutes with matrix-vector
multiplication. Matrix identities give the identity and multiplication laws,
and linearity preserves the additive group law of the vector group. The
resulting `automorphicAction` is an actual automorphic group-scheme action;
`schemeAction` retains its morphism in the categorical action structure.

`coordinatePoint` is the constant coordinate vector \(e_j\) on every scheme test.
`orbitMap` is its actual orbit morphism from the group to the affine vector
group. `coordinates_comp_orbitMap` proves that its composition with any test
point \(g\) has coordinates \(\rho(g)e_j\). The all-test theorem
`orbitMap_fibers` says that the images of \(g\) and \(h\) agree if and only if
\(\rho(g^{-1}h)e_j=e_j\). Its proof applies the invertible matrix
\(\rho(g)^{-1}\), with the converse obtained by applying \(\rho(g)\).

These are derived constructions and identities, with no additional literature
assertion. They supply an affine ambient scheme and exact stabilizer fibers;
they do not establish closedness of the orbit, affineness of a quotient, or
existence of a quotient.
