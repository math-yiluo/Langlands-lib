# Group structure and dimension on actual homogeneous quotients

This internal adapter is derived from `NormalQuotient.groupScheme`,
`NormalQuotient.hom`, `NormalQuotient.isFppfQuotient`, and the existing
`RelativeRoot.IsFppfQuotient.exists_action_relativeDimension_of_kernel`.
Worker 362 authored the adapter. It adds no quotient existence assumption to
the supplied `HomogeneousQuotient` data.

For an actual homogeneous quotient `D` of `i : H → G` over any scheme, normality
of `SubgroupFunctor.range i` descends the group structure to precisely
`D.scheme`. The homomorphism `groupProjection` has precisely `D.projection`
as its underlying morphism. The projection remains smooth, surjective and
quasi-compact, and its represented fppf kernel is exactly the specified range
on every scheme test. This follows by supplying the smoothness, surjectivity,
quasi-compactness and exact coset fibers already contained in `D` to the
existing normal-quotient construction. Smoothness supplies local finite
presentation. If the base and the actual quotient scheme are affine, the
descended group has an affine structural morphism.

Over any field in any universe, `exists_action_relativeDimension` applies to
an affine connected unipotent source, a monomorphic subgroup inclusion, and
an affine homogeneous quotient with normal subgroup range. An action of any
group scheme preserving that range descends to the quotient. Given source
smooth dimension `d` and subgroup smooth dimension `n > 0`, the quotient is
affine, smooth, connected and unipotent. Its projection is smooth of relative
dimension `n`, and its own smooth dimension `m` satisfies `d = n + m` and
`m < d`. Equivariance holds on every relative scheme test. The proof uses the
exact represented kernel to apply the existing action and dimension theorem.
No torus, centrality, algebraic closure or subgroup connectedness is needed
for this adapter.
