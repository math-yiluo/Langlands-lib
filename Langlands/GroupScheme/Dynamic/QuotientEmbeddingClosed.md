# Closed images of supplied dynamic quotient comparisons

Worker 708. This internal derived unit treats the actual comparison
`Dynamic.suppliedQuotientMap` between supplied quotients. It retains exact
right-coset fibers on every relative test scheme.

Over any base, when both projections are fpqc, the comparison respects
the left quotient actions. The proof checks the equality after an fpqc
local lift through the source projection and uses multiplication on
lifted cosets. Surjectivity of the source projection identifies the
comparison's topological image with the image of the ambient projection
restricted to the subgroup.

Over an algebraically closed field, suppose the source group is smooth,
the source projection is smooth, surjective and quasi-compact, the source
target has quasi-compact structure map, and the ambient quotient is locally
of finite type with fpqc projection. A closed subgroup embedding gives a
monomorphic comparison. If the restricted ambient projection has closed
image, `suppliedQuotientMap_isClosedImmersion_of_closed_range` proves the
comparison is a closed immersion. Smooth descent makes the supplied source
quotient smooth and therefore reduced. Surjectivity gives rational
transitivity over the algebraically closed field. The published general
homogeneous closed-immersion theorem then applies to the equivariant
monomorphism with closed image. No separate immersion premise remains.

If the ambient projection is also smooth and its dynamic parabolic has an
actual representative `i`, the closed-image hypothesis follows from
closedness of the multiplication image of the source subgroup and `i` in
the ambient group. The proof uses the published cartesian product-quotient
square and smooth surjective descent of closed subsets. The final theorem
composes this closed immersion with a proper ambient structure map to prove
properness of the same supplied source quotient.

`suppliedClosedQuotientComparison_of_product_closed` packages the actual
comparison morphism together with its closed immersion property and its
compatibility with the two supplied projections. It is a subtype value
constructed from the preceding lemmas and the published comparison
factorization; it retains the same source and target schemes.

This unit does not prove the multiplication image closed. It reduces the
remaining scheme-level comparison obligation to that topological geometric
input; it supplies no proof of `DynamicQuotientProperStatement`. The proofs
use general quotient descent, homogeneous geometry, dynamic functoriality
and smoothness. They use no regular-cocharacter/Borel or rank-one result.
All cocharacters, including trivial and central cocharacters, are retained.
The provenance is internal composition of these published interfaces;
no new external source theorem is asserted.
