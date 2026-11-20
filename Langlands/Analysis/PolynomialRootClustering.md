# Clustering roots of nearby monic polynomials

For a tuple \(a\) of length \(n\) over a commutative ring, `monicRootPolynomial a` is the product of the factors \(X-a_i\). The map `monicRootsToCoeffs` records its coefficients of degrees \(0,\ldots,n-1\). The monic degree-\(n\) term is fixed. Over a domain the polynomial has root multiset given by the tuple, with multiplicity. A split monic polynomial of degree \(n\) has such a tuple by enumerating its root multiset.

Over a proper normed field the coefficient map is proper. The coefficient formula for multiplication gives continuity by induction on the number of factors. The Cauchy bound bounds each root norm by one plus the largest of the recorded coefficient norms, so the inverse image of a compact coefficient set is closed and bounded. It is compact in the product with the supremum norm.

The fiber of the coefficient map over the coefficients of a tuple consists of its permutations. Equality of coefficients yields equality of the monic polynomials, hence equality of their root multisets. Equal counts give bijections between the index fibers of each root value, which combine to give a permutation of all indices. For each positive radius, the union of balls of that radius around the permutations is an open neighborhood of this fiber. Properness makes the coefficient map closed, so all fibers over sufficiently nearby coefficients are contained in this neighborhood. This recovers local root matching with multiplicity even at repeated roots.

This internal result supplies the root-continuity step for local spectral clusters of matrices. The proof uses the Cauchy bound and the closed-map neighborhood lemma from Mathlib.
