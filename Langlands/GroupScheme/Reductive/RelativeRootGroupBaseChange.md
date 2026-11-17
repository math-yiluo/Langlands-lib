# Arbitrary scalar extension of actual dynamic root groups

This internal helper concerns the actual dynamic group `Uc i mu nu` in an affine group over an arbitrary commutative ring. It imposes no root-datum or reductivity hypotheses.

The composite inclusion `incl i mu nu` represents the intersection of the dynamic centralizer of the cocharacter `mu` with the ambient dynamic unipotent subgroup of `nu`. For the forward inclusion, the chosen centralizer and unipotent representatives supply the two memberships. For the converse, the centralizer representative lifts a point to the centralizer, and reflection of dynamic unipotent membership through its closed immersion lifts that point to `Uc`.

Subgroup functor intersections, dynamic centralizers and dynamic unipotent subgroups commute with arbitrary base change. Their representing inclusions therefore represent the same subgroup after any extension of commutative rings. `rootGroupBaseChangeIso` is the resulting isomorphism from the scalar extension of the original actual group to the newly constructed actual group. `rootGroupBaseChangeIso_hom_comp` identifies their inclusions into the scalar extension of the ambient group.

The provenance is internal: the construction combines the existing actual dynamic representatives, closed-immersion reflection, arbitrary base-change identities and uniqueness of represented subgroup functors. It does not assert fppf-local generation or supply a global additive coordinate.
