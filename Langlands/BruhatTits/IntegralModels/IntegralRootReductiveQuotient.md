# Integral root models in the actual reductive quotient

This internal supporting module concerns a single relative-component model pair
`D` over a local domain `R` with fraction field `K`, an actual compatible integral
split torus `A : IntegralSplitTorusData D.neutral i`, and supplied quotient data
`Q : SpecialFibreQuotientData D` satisfying `Q.IsReductiveQuotient`.
The universe is arbitrary. No apartment, facet or root-occurrence premise is used.

`SpecialFibreQuotientData.projection_smooth` proves smoothness of the specified
projection `Q.projection`. The validity predicate says that its kernel is
represented by the supplied smooth unipotent radical. Closedness of the radical
inclusion gives its full all-test representability. Affineness of source and
target makes the projection quasi-compact, so the represented fppf quotient
smoothness theorem applies. This proves smoothness of the actual projection,
without replacing it by an abstract isomorphic quotient.

For any nonzero generic character `a`, `A.rootReductiveQuotientMap Q a ha` is
the composite of the actual special fibre of `A.rootModelMap a ha` with
`Q.projection`. The root model and map are the constructions of
`IntegralRootFiltration`; `IntegralRootSpecialFibre` identifies this very
special-fibre inclusion with the full root functor for the character
`A.characterSpecialization a`.

`rootReductiveQuotientMap_smooth_kernel` proves smoothness of the entire
scheme-theoretic kernel of that original composite, including infinitesimal
test points. The neutral special fibre and quotient are smooth affine groups,
the residue torus is split, and specialization preserves nonzero characters.
A smooth closed representative of the target root functor exists for every
such character. Applying `RelativeRoot.SmoothQuotient.smooth_kernel_comp` to
these actual maps yields the claim. The ambient projection is a scheme
surjection because it is the represented fppf quotient.

`rootReductiveQuotientMap_lie_range` identifies the range of the actual
residue-field linear differential with the target positive cyclic weight span
for conjugation through `A.specialFibreInclusion ≫ Q.projection`. This span is
the sum of the weight spaces for positive integer multiples of the specialized
character. The proof applies `RelativeRoot.SmoothQuotient.lie_range_comp` to
the smooth projection and the full represented source root.

Finally, `rootReductiveQuotientImage_lie_range` gives the same equality for the
closed inclusion of the actual schematic image of the original composite.
The source root special fibre is smooth and connected by the integral root
model's geometric connectedness. The just-proved full-kernel smoothness
allows `Lie.range_schematicImage_inclusion_of_smooth_kernel` to identify the
two differential ranges. No inference from smoothness of the image alone is made.

The module derives these facts from the imported constructions and quotient,
root-representability and Lie-image theorems. It asserts no new correspondence
with external literature. For the common-torus facet theorem, the incident
model map, root survival as a function of facet direction, and the full
incident image's weight support remain to be identified.

The unchanged smoothness statement `SpecialFibreQuotientData.projection_smooth`
is reused from [ReductiveQuotientRoots](ReductiveQuotientRoots.md).
