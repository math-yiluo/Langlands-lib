# Norm-one inclusion for actual adelic subgroups

This internal construction applies to an arbitrary number field and an actual
subgroup functor of an affine finite-type group scheme. Its evaluated adelic
subgroup is assumed closed, and its actual quotient by its principal rational
image is assumed compact. It does not require the subgroup functor to be normal
or its rational image to equal all rational points of an abstract presentation.

The existing compact-cover theorem gives a compact set meeting every principal
orbit. Every ambient rational algebraic character has normalized adelic norm one
on principal rational points by the product formula. Its image on the evaluated
subgroup therefore equals the image of the compact orbit cover. A compact
subgroup of positive real units is trivial. Applying this to every actual
ambient character proves inclusion in the existing norm-one subgroup.

`normOneInclusion` is the actual continuous subgroup inclusion with restricted
codomain. Its value in the full adelic group is unchanged, and it sends each
actual rational point to the existing ambient principal norm-one point.
`normOneInclusion_rational_mem` records the resulting actual principal-subgroup
compatibility needed for quotient periods.

The argument adapts the published compact-quotient proof in
`AdelicLeviFiniteVolume.mem_normOneSubgroup_of_compactSpace` to evaluated subgroup
functors. It uses the published actual subgroup topology, product formula and
compact positive-character theorem. This is internal infrastructure for the
compact radical periods in Getz–Hahn, Section 9.2 (printed pp.243–246), with the
registered October 2026 errata's compact-quotient convention. It does not assert
smoothness, construct period measures, prove almost-everywhere period
convergence or identify the full automorphic cuspidal L2 space.
