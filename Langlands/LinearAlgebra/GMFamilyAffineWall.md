# Cancellation at a wall of intercepts

`AffineBases.extendedSum_eq_of_preservesStrict` compares the weight sums at two
intercept arrays with the signs of their strict slacks preserved at a common
wall point. A regular direction gives the sign when a slack vanishes. At a
simple wall all vanishing outside slacks are proportional. Since the slacks
outside one basis are pairwise nonproportional, the set of tight labels at an
intersection is either the basis itself or the basis with one extra label.

The proof groups the sum by the tight set. For the augmented set, every basis
in its group is obtained by deleting one label with nonzero dependence
coefficient. Its summand contains the absolute value of that coefficient and
the imaginary parameter of the deleted normal. The two sign choices select
the negative and positive coefficients. These sums agree because the
augmented normals satisfy the coordinate dependence. The argument is a
finite linear algebra identity on the intercepts and weights of
`GMFamilyAffineBases`.
