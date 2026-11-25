# Lifting subgroups of multiplicative type through nilpotent thickenings

`Langlands.GroupScheme.multiplicativeTypeSubgroupInfinitesimalLift` has type
`Langlands.GroupScheme.MultiplicativeTypeSubgroupInfinitesimalLiftStatement.{u}`.
It proves existence of flat subgroup lifts, reflection of multiplicative type,
and conjugacy of flat lifts by a point reducing to the unit. The base is the
spectrum of any commutative ring in universe `u`, and the ambient group is smooth
over that base. The statement records the correspondence with SGA 3, Exposé IX,
Théorème 3.6 bis and Corollaire 3.3 bis, recomposed pp. 39–40.
[Statement and source](MultiplicativeTypeSubgroupInfinitesimalLiftStatement.md)

The proof follows the reduction in SGA 3, IX, 3.6 bis to lifting groups of
multiplicative type, lifting homomorphisms into a smooth group, and reflecting
immersion across a nilpotent thickening. In Lean, the local proof of homomorphism
lifting and conjugacy applies `HomScheme.multiplicativeTypeInfinitesimalLift_of_cohomology`
to low-degree cohomology vanishing, the square-zero deformation theorem, and
flatness and affineness of groups of multiplicative type. The reduction iterates
the square-zero result for the nilpotent ideal.
[Cohomology reduction](../HomScheme/InfinitesimalCohomologyReduction.md),
[vanishing](../Cohomology/MultiplicativeTypeVanishingProof.md),
[square-zero deformation](../HomScheme/SquareZeroCohomology.md),
[source geometry](RelativeMultiplicativeTypeGeometry.md)

For existence, `multiplicativeTypeNilpotentEquivalence` supplies a flat
multiplicative-type group over the original base and an isomorphism from its
reduction to the given source. Compose the reduced inclusion with this
isomorphism and lift the composite as a homomorphism. The composite is an
immersion, so immersion reflection gives an immersed lift. Precomposition with
the isomorphism preserves the range of the inclusion on points. For the second
clause, `multiplicativeTypeFlatNilpotentReflection` applies directly to the
given flat group and its reduction.
[Nilpotent equivalence](MultiplicativeTypeNilpotentEquivalenceProof.md),
[immersion reflection](../../AlgebraicGeometry/ImmersionNilpotentReflection.md),
[flat reflection](MultiplicativeTypeFlatNilpotentReflectionProof.md)

For conjugacy, both reductions are immersions by base change. Their equal ranges
give an isomorphism between the two reduced sources that commutes with their
inclusions. This identifies the second reduction as a group of multiplicative
type, and flat reflection applies to both original sources. The private
`liftMultiplicativeTypeIso` lifts the reduced isomorphism and its inverse using
surjectivity on homomorphisms. Injectivity verifies their inverse identities.
After precomposing the second inclusion by the lifted isomorphism, the two
inclusions agree on reduction. Homomorphism conjugacy gives the desired point,
and invariance of the range under the lifted isomorphism gives the equality of
subgroup functors. [Represented subgroups](../RepresentedSubgroup.md)
