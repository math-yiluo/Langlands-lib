# Spherical irreducible quotients of ordered unramified principal series

This internal construction supplies an actual irreducible spherical quotient of
`principalSeriesOfTuple F z` whenever the nonzero complex parameters have
weakly increasing norms. Repeated characters and distinct equal-norm characters
are permitted. The field universe is arbitrary. This construction establishes
quotient existence and sphericality; spherical generation is a separate step.

The spherical dual embedding construction supplies an admissible smooth
irreducible object `B` embedded by an actual injection into the smooth dual of
the actual principal series `A`. It also supplies a nonzero spherical fixed
vector of `B`. The principal series is smooth and admissible, and compact open
subgroups of the actual p-adic general linear group are cofinal.

Worker 706's generic dual-quotient construction now applies. Pullback of smooth
functionals along the injection, composed with the canonical map into the smooth
bidual of `A`, gives an actual surjection from `A` onto the smooth contragredient
of `B`. Admissible smooth duality preserves irreducibility. Compact fixed-space
duality supplies a nonzero spherical fixed vector in that target. The theorem
`exists_spherical_irreducible_quotient` retains these actual quotient witnesses;
`sphericalQuotientDatum` chooses the resulting smooth object with its
irreducible-quotient and nonzero-fixed-space proofs.
