# Smooth-vector density in the original full cusp L2 space

Worker 116 states
`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2SmoothDensityStatement`
for a number field in arbitrary universe `u` and an actual connected
reductive group scheme. It keeps the affine locally finite-type hypotheses,
the structural `ParabolicDynamicStatement` `hPD`, the commutative group scheme
`T`, central morphism, injective character restriction of finite-index range,
actual split-torus isomorphism and norm-one right-Haar invariance required by
the existing full cusp L2 construction. The target does not discharge those
original hypotheses.

The Hilbert space is the unchanged `fullAEL2CuspidalSubmodule`, written `C`,
of the original `Lp ℂ 2` null classes for the positive rational quotient Haar
measure, with its inherited norm and subspace topology. Its cusp condition
still requires separate almost-everywhere absolute convergence and vanishing
of periods for every actual proper rational parabolic. The infinite action is
exactly `fullAEL2CuspidalInfiniteRightAction`, the bounded original full cusp
action restricted along the actual infinite inclusion. Its manifold is
precisely `InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG`, with the
chosen `hG.smoothDimension` and original completion scalar instances, as in
`GroupSchemeQuotientL2SmoothDensityStatement`. There is no split or
quasi-split hypothesis on `G`.

The conjunction asserts two norm-density results in the same cusp space
`C`. First, the existing real-manifold smooth-vector subspace
`Langlands.Archimedean.smoothVectors` for the original infinite cusp action is
dense in `C`. Second, the vectors of that subspace which are also
`Langlands.IsSmoothVector` for the existing finite cusp action
`fullAEL2CuspidalFiniteRightAction` are dense in `C`. The finite condition
means that some actual open subgroup of the finite point group fixes the cusp
vector; it is not the real-manifold condition. Both smoothness conditions are
for actions on `C` itself, so the orbit maps take values in `C`.

This is an internal cusp analogue of the published ambient target. A proof
route from that ambient target is as follows. The original subtype-valued
orthogonal projection onto `C` is a continuous linear surjection, being the
identity on `C`. By `fullAEL2CuspidalOrthogonalProjection_infiniteRightAction`
and the published full-adelic law `fullAEL2CuspidalOrthogonalProjection_rightAction`
it intertwines the ambient and cusp infinite actions and the ambient and cusp
finite actions. Composing an ambient smooth orbit with this continuous linear
map gives a smooth cusp orbit, and a fixed ambient vector projects to a fixed
cusp vector. The image of a dense set under a continuous surjection is dense,
so both conjuncts follow from the two ambient density conjuncts. This is a
proof route, not a proof supplied by this proposition definition, and it
depends on the still unproved ambient target.

No arbitrary measure, replacement Hilbert space, chosen abstract action,
changed cusp condition, changed manifold or transported finite smoothness
notion occurs in the conclusion. The target supplies no pointwise smooth
representative, literal algebraic tensor realization, compact-type finiteness,
finite-volume theorem, differential growth, rapid decay, admissibility,
compactness, trace or spectral decomposition.
