# Vanishing of unwanted Jacquet inertia components

Worker 137. Supporting construction for Task 5352.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version of 9 July 2026, source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, VI.7.2 Proposition and proof, printed pp.184–185 / PDF pp.190–191. This is a derived internal comparison between the original component-vanishing condition and the published target's subquotient-exclusion formulation, conditional on the genuine inertia decompositions used by the source.

For a supplied `IsRationalInertiaCategoryDecomposition G π`, `rationalInertiaComponentFamily` chooses the actual two components of a smooth object from the existing decomposition proposition. Its `true` component satisfies the all-subquotients inertia-block property, and `false` satisfies the complementary no-subquotients property. `rationalInertiaComponentCofan` and `rationalInertiaComponentIsColimit` retain the original object as the vertex and the actual universal property. The construction asserts no existence of that decomposition.

`rationalInertiaComponent_isZero_iff_complement` proves that the chosen block component is zero exactly when the original object has no irreducible subquotient in the fixed inertia orbit. If the original object has the complement property, the component embeds in it by the coproduct inclusion and hence has both block and complement properties. Existence of an irreducible subquotient of a nonzero smooth representation forces it to be zero. Conversely, identify the object with the actual direct sum of the two components. An irreducible subquotient comes from one component: the zero block component is impossible, so it comes from the complement. This works at arbitrary independent field and carrier universes, without admissibility or finite length.

For the standard-family objects and saturated carriers of Task 5352, `bernsteinJacquetExclusion_iff_zero_inertiaComponents` applies this comparison to the scheme-side normalized Jacquet module of every prohibited datum. It combines the preceding unconditional comparison relative to supplied decompositions with the proved `bernsteinJacquetExclusion_iff_inertiaComplement`. Thus the published condition (iii) is exactly vanishing of those unwanted components whenever the genuine Levi inertia decompositions are supplied. The source's zero vector-space assertion is expressed by `IsZero` in the actual smooth category.

No Bernstein-block membership equivalence is proved here. The required Levi inertia decompositions remain an explicit premise; the original target and its import closure remain unchanged. Choosing another cofan satisfying the same component conditions gives the same vanishing criterion by the same proof, so the criterion does not depend on the choice.

The local instances have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and local
instance scope are unchanged.
