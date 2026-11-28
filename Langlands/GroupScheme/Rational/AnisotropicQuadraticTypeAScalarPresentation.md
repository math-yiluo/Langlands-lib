# Scalar Hermitian presentations over a quadratic splitting field

`AnisotropicQuadraticTypeAScalarPresentationStatement` gives an actual special unitary presentation for an anisotropic simply connected affine group of locally finite type over an infinite field. The group must have a split pinning of type A of rank at least two over a quadratic Galois extension. The Hermitian matrix is nonsingular and is defined over that same extension.

Choose a maximal ground-field torus that splits over the quadratic field, and give it a Tits index with the trivial maximal split torus. Transport the type A numbering from the supplied split pinning by a Weyl conjugacy of bases. This supplies a pinned coordinate isomorphism from the special linear group over the prescribed quadratic field.

Anisotropy makes the nonidentity Galois element act by negation on the torus characters. In type A of rank at least two, negation lies outside the Weyl group, so the corresponding star action moves a vertex. The matrix discrepancy is therefore of inverse-transpose type. The action over the identity element has trivial discrepancy. Hermitian descent then gives the special unitary presentation over the ground field, using the nonidentity element as the involution of the quadratic field.

The rank-two application is the scalar presentation of the subgroup in Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, §6.8, Lemma 6.31, printed p. 380. [Chapter 6](https://www.sciencedirect.com/science/article/pii/S0079816908620711)
