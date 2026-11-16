# Transport of the universal largest subtorus

Worker 632. These are internal, derived lemmas for the arbitrary-base largest
subtorus proof. They do not assert that a universal subtorus exists.

`IsUniversalSubtorus.factor` specializes universality to the identity base map,
then uses the natural pullback identity isomorphism to obtain a factorization
over the original base. `baseChange` applies universality to the composite of
two base maps and transports the factor through the natural comparison between
composite and sequential pullback. Closedness and the relative-torus condition
use their published arbitrary-base-change lemmas.

`iso_comp` and `comp_iso` transport universality through source and ambient group
isomorphisms. Their factors use the inverse of the pulled-back isomorphism.
`of_factor` shows that any closed relative torus through which the universal
inclusion factors also has the universal property: pull back that factor and
compose each existing factorization with it.

`range_le` expresses factorization as containment of subgroup functors on every
test scheme. `range_eq` obtains equality for two universal representatives by
mutual containment. `of_range_eq` transfers the property to a closed relative
torus representing the same subgroup functor, using the published factorization
through a represented subgroup. `isLargest` forgets the stronger requirements
and yields exactly the conjunction used by the local predicate in
`RelativeMultiplicativeTypeLargestSubtorusStatement`.
