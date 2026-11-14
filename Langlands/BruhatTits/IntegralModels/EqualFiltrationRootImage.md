# Actual special-fibre root images at equal filtration subgroups

This is derived infrastructure for the parabolic-image proof. It uses the
published comparison isomorphism for smooth root-filtration models with equal
integral-point images, generic rigidity of integral-model maps, the actual
special-fibre functor, and the canonical schematic-image factorization.
No new assertion is attributed to external literature.

Fix two supplied `RootFiltrationModelData` values `U` and `V` for the same
apartment point and relative root, at possibly different depths `r` and `s`.
The hypothesis is equality of the actual ambient filtration subgroups at those
depths. It need not be equality of the real numbers. Both models are smooth by
their supplied data. Over a general domain with fraction field, retain the
explicit smooth homomorphism extension criterion `hext`.

Let `N` and `N'` be actual integral models of the same generic group, with an
identity-generic-fibre map `ψ : N' → N`. Supply compatible root-model maps
`φ : U.model → N` and `φ' : V.model → N'`. Their generic maps are the original
root inclusions; they are not arbitrary maps into the ambient generic group.
No closedness of these two supplied integral maps is needed by this result.

The published `modelIsoOfFiltrationEq` gives an actual integral-model
isomorphism from `U.model` to `V.model`. The new
`modelIsoOfFiltrationEq_hom_comp` proves that its homomorphism, followed by
`φ'` and `ψ`, is exactly `φ`. The proof checks equality on generic fibres and
uses the rigidity of maps into an affine integral model.

When the domain is local, `specialFibreImageFactorOfFiltrationEq` composes the
special fibre of that isomorphism, the actual special-fibre map of `φ'`, and
the canonical projection onto the schematic image of `ψ.specialFibreMap`.
Its compatibility theorem proves that composing with the canonical closed
image inclusion gives `φ.specialFibreMap`. Thus
`range_specialFibreMap_le_image_of_filtration_eq` is containment of the full
subgroup functors on every test scheme. It concerns the image of the root
model's special fibre; identifying that image with a particular residue-root
subgroup remains a separate obligation.

The three `unramified` declarations specialize to the actual integers of the
inertia fixed field of a nonarchimedean local field. They discharge `hext`
with `fixedField_hasSmoothHomExtension smoothHomExtension`, using the
published proof. They retain the supplied root models, the compatible maps,
and equality of the actual filtration subgroups.

This unit proves neither the facet geometry that gives the necessary
filtration equalities nor the Borel containment needed for parabolicity.
It does not assert rational surjectivity of any schematic-image projection
or the final `UnramifiedFacetParabolicImageStatement`.
