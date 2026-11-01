# Internal block-root support for actual induced sections

This internal derived module applies smooth simple-root support to the actual
block tensor and scalar-section constructions used for the JPSS two-block
integral. It is motivated by JPSS (1983), Section 4.6 and Section 4.10(2), but
its uniform integer-bound formulation is an auxiliary result of this development.

`exists_blockTensor_rootBounded` chooses one natural bound for both blocks of
an arbitrary tensor contraction. It is uniform in the diagonal uniformizer
exponents and in both right integral block factors. Each pure tensor uses
smooth simple-root support for its actual coefficient-image vectors. The
scalar multiplier and the product formula imply that nonzero contraction
requires every factor to be nonzero. Tensor addition uses the maximum of the
two bounds, since a nonzero sum has a nonzero summand.

A section has finitely many values on the compact integral subgroup, by local
constancy. `exists_integral_blockTensor_rootBounded` takes the supremum of the
bounds for these values, giving one bound before the integral element and all
torus exponents.

`IsSectionTorusRootBounded` is the actual scalar-section support predicate.
It bounds adjacent exponent increases inside each original block whenever the
oppositely twisted scalar section is nonzero at a torus element followed by
an integral element. The existence theorem uses the inverse-standard block
functionals as standard functionals for the negative additive character.
Scalar-section covariance and the exact opposite-twist formula reduce a
nonzero section value to a nonzero untwisted block tensor contraction. Only
smoothness of the block representations is assumed; neither nonzero
functionals nor irreducibility are required. The field and representation
universes are independent.

No common opposite cone, rectangle volume, analytic convergence or Laurent
identity is asserted here.
