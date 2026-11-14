# Reduction of every integral generic-root section

This derived construction works over an arbitrary local domain with a specified
fraction field, in any universe. The ambient integral model is smooth, and an
actual split integral torus maps to it. For a nonzero integral character, any
integral ambient section whose generic point belongs to the corresponding
intrinsic root functor factors through the closed integral root model.

`exists_integral_section_of_generic_mem` uses the generic representability from
`SplitRoot` to lift the generic point into that root model. Its integral inclusion
is closed, so `ClosedSubgroupIntegralPoints.exists_eq_of_integralPointMap_eq`
factors the original integral section through it.

`reduction_mem_of_generic_mem` base changes the integral root representation
to the residue field. Full root-functor base change identifies it with the root
functor for the actual specialized torus map and specialized character.
Naturality of base change then places the reduction in that functor.

`integralRootSections` is the subgroup of all such ambient integral sections,
defined as the inverse image of the generic root functor under the actual
integral-point map. `rootReduction` restricts the actual reduction homomorphism
to this subgroup, with codomain the specialized intrinsic root group.
`rootReduction_coe` records that it retains the original reduction.

The proof uses only the named existing interfaces and subgroup restriction.
There is no Henselian, algebraically closed residue-field, maximality or
reductive-quotient hypothesis. The construction asserts containment after
reduction, without surjectivity or any strict-depth kernel or facet-survival
claim.
