# Rational Weyl factors for matching elliptic tori

Let \(F\) be a nonarchimedean local field of characteristic zero and \(D\) a
finite-dimensional central division \(F\)-algebra with its \(F\)-module
topology. For \(g\in GL_n(F)\) and \(g'\in D^\times\) satisfying
`Corresponds F D g g'`, the map `Corresponds.centralizerEquiv` is the
topological group isomorphism induced by the centralizer algebra isomorphism
sending \(g\) to \(g'\). It identifies their regular points, and the ordinary
characteristic polynomial of each split torus point equals the reduced
characteristic polynomial of its image. The two finite rational normalizer
quotients have equal order. These orders give the denominators of the torus
weights in Badulescu's elliptic pairing.

The characteristic polynomial comparison uses a finite Galois splitting
field for \(D\). Over that field the matrices representing \(g\) and \(g'\)
are conjugate by squarefree matrix conjugacy. A cyclic vector for \(g\)
expresses every element of its centralizer algebra as a linear combination
of powers of \(g\). The centralizer algebra isomorphism and the matrix
conjugation send \(g\) to the same image, so they agree after extension
on the chosen torus point. Invariance under conjugation and injectivity of
polynomial coefficient extension give
`Corresponds.centralizerEquiv_charpoly_eq` over \(F\).
The division reduced polynomial is irreducible whenever it is separable.
Thus `Corresponds.on_centralizerEquiv` identifies the regular torus points
by the same matching relation as the original pair.

For a point with commutative centralizer, any conjugate of the point
inside the centralizer has the same centralizer. Orbit–stabilizer identifies
the normalizer quotient with the set of those conjugates.
`Corresponds.rationalWeylGroupEquiv` compares these sets using the torus
isomorphism. On the split side, equality of characteristic polynomials
gives conjugacy by squarefree matrix conjugacy. On the division side,
the common irreducible reduced polynomial gives two embeddings of
its root field, which are conjugate by Skolem–Noether.
`Corresponds.natCard_rationalWeylGroup_eq` gives equality of the two
cardinalities used in the Weyl weight.

## Source

Alexandru Ioan Badulescu, *Correspondance de Jacquet–Langlands pour les
corps locaux de caractéristique non nulle*, Annales scientifiques de
l'École normale supérieure 35 (2002), §6, pp. 745–746, the torus
denominator and the isometry of the matched elliptic pairings.
