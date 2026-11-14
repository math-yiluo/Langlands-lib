# Integral lifting for parabolic images of descended facet models

This is an internal derived construction at arbitrary universe `u`. It combines
the existing actual schematic-image lifting criterion, the positive-subgroup
criterion, and the conditional facet-image parabolicity theorem. It claims no new
translation of an external source.

For any identity-generic morphism `φ` between relative-component model pairs over
a Henselian local domain with perfect residue field,
`hasParabolicReductionPreimage_of_unipotentKernel_of_reductivePositivePoints_le`
assumes that the full kernel of the actual neutral special-fibre map is smooth,
connected and unipotent. It also assumes containment of the target positive
subgroup in the source positive subgroup for every pair of actual maximal
reductive quotients. The published special-fibre image projection theorem makes
the projection onto the actual schematic image surjective on residue-field
points. The published positive-subgroup criterion chooses reductive quotients
and proves that the inverse image of the image's residue points under reduction
is exactly the range of the integral-section homomorphism.

`unipotentKernelReductionPreimageLift` chooses a source integral section from this
equality for a supplied target integral section whose reduction lies in the
actual image. Its specification states that the integral-section homomorphism
maps the lift to the supplied section itself. The construction requires no
chosen quotient as an extra input; the universal positive-subgroup hypothesis
retains all quotient conditions.

For incident descended facets,
`unramifiedFacetParabolicImage_of_generation_kernel_positive` combines this
lifting result with
`unramifiedFacetImage_isParabolic_of_upstairs_rootGeneration`. It retains the
complete upstairs radical-root generation statement as a premise, and also
retains the full kernel and universal positive-subgroup inputs for the supplied
map. Its model characterizations are the exact integral-point equalities after
maximal-unramified coefficient extension. The map assumptions are equivariance,
apartment compatibility and the exact restricted-facet equality. The local-field
valuation ring is Henselian by `henselianLocalRing_integer`, and its finite
residue field supplies perfectness.

Finally,
`unramifiedFacetParabolicImage_of_generation_positive_kernelCriterion` concludes
the exact existing `UnramifiedFacetParabolicImageStatement`. Its explicit
premises are the full upstairs generation statement, the full
`UnramifiedFacetPositiveRadicalStatement`, and
`UnramifiedFacetKernelCriterion`. The last is a proposition definition,
universally quantified over the characterized incident facet models in the
preceding paragraph. It retains equivariance, apartment compatibility and
restricted-facet equality, and asks for the smooth connected unipotent kernel
condition for every supplied model morphism. The unit defines this requirement
without asserting it.

The proof introduces every binder of the original target, retaining all seven
building hypotheses, all eight apartment-descent hypotheses and the supplied
model smoothness hypotheses. It specializes the positive-radical statement with
all those inputs, specializes the kernel criterion with the required subset of
them, and proves the two conjuncts by the preceding parabolicity and lifting
results.

`unramifiedFacetKernelCriterion_of_modelKernel` specializes the imported
`unramifiedFacetKernel_of_modelKernel` to all the criterion's binders. That
imported theorem constructs an actual common chart with bounded upper subset
and closure incidence, applies the full model-kernel statement to the actual
coefficient-extended neutral models and map, then reflects the full kernel
properties through the residue-field extension.

Consequently,
`unramifiedFacetParabolicImage_of_generation_positive_modelKernel` concludes the
exact original target from precisely three explicit full statement premises:
`UnramifiedUpstairsRadicalRootGenerationStatement`,
`UnramifiedFacetPositiveRadicalStatement`, and
`UnramifiedModelKernelStatement`. It composes the two preceding deductions. No
target or imported statement is modified. The unconditional target remains open
until these three inputs have been proved.
