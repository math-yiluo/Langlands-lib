# Equivariant normal unipotent quotients from closed vector orbits

This internal theorem, authored by Worker 362, combines
`Chevalley.unipotentAffineQuotient` with
`HomogeneousQuotient.exists_action_relativeDimension`. The exact published
`UnipotentAffineOrbitClosedStatement` remains an explicit input.

Over every algebraically closed field in every universe, let `G` be affine,
connected and unipotent, smooth of dimension `d`. Let `i : Z → G` be a closed
unipotent subgroup, smooth of dimension `n > 0`, whose all-test range is normal.
Every actual action of any group scheme `A` on `G` preserving this range has an
actual equivariant quotient `q : G → Q`. The quotient is affine, smooth,
connected and unipotent. Its represented fppf kernel is exactly
`SubgroupFunctor.range i`, its projection is smooth of relative dimension `n`,
and it has smooth dimension `m` with `d = n + m` and `m < d`. Equivariance is
proved on every relative scheme test.

The proof constructs an affine homogeneous quotient using the vector orbit
and the supplied closed-orbit proposition, puts the descended normal group
structure on that precise scheme, and applies the existing represented-kernel
action and dimension theorem. Subgroup unipotence is retained explicitly:
this unit does not prove that it follows from the ambient group's unipotence.
It does not prove the closed-orbit proposition, descend affineness to an
arbitrary field, or prove the host ordered-product statement.
