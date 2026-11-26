# Invariance under changing the intercepts

`AffineBases.sum_normalizedWeight_eq` shows that the sum over feasible bases
of the Gram volume divided by the product of the parameter evaluations on
that basis is independent of the generic intercepts. All normal evaluations
in the denominator are assumed nonzero. `sum_weight_eq` first proves the
identity after multiplication by their common product.

To compare two regular arrays, the proof chooses an endpoint with the same
strict signs as the second array. It simultaneously avoids all nonzero
crossing determinant forms, following the same determinant computation as
`FiniteHyperplaneSegment` over the real intercept space. Every point of the
resulting line has only proportional vanishing outside slacks. Along this
line the extended weight sum is locally constant by the wall cancellation
of `GMFamilyAffineWall`, using the fixed regular start direction for ties.
Preconnectedness of the real line gives the endpoint equality. At regular
arrays the extended sum is the ordinary feasible-basis sum.
