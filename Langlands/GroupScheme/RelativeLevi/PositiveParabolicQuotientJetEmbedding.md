# Stabilizing parabolic jets above any prescribed order

For a point of a corepresented group, `Corepresented.Stabilizes.of_le`
shows that stabilization of a higher subgroup identity jet implies
stabilization of each lower jet. It iterates the proved successor
implication.

Given `ProperQuotientJetData D` for an actual subgroup and its supplied
proper homogeneous quotient, `D.atLeast m` constructs data at order
`max D.order m`. Stabilization at this order implies stabilization at the
old order, hence membership in the actual subgroup. Conversely every
subgroup point stabilizes each of its identity jets. Thus the exact
all-algebra stabilizer remains the same subgroup.

Smoothness of the ambient group and of the retained quotient coordinate
algebra gives finite projectivity of both new jet modules. The existing
quotient projection still has its exact all-test coset fibers. Applying
the concrete quotient embedding construction therefore supplies a new
finite projective complement, represented Grassmannian and closed
embedding of the same actual quotient, with its exact orbit-map
factorization. The new Grassmannian and complement are allowed to depend
on the larger order.

`affineParabolicQuotientJetDataAtLeast hG i hi m` applies this construction
to the actual affine-base parabolic quotient. It adds no hypothesis to
the earlier parabolic data construction. Taking `m = 1` gives a positive
stabilizing order. Neither an actual jet-sheaf comparison nor determinant
positivity is asserted here.

This is an internal refinement of the existing finite-stabilization and
actual quotient-embedding constructions. Its only additional argument is
the monotonicity of jet stabilizers together with stabilization by
subgroup points.
