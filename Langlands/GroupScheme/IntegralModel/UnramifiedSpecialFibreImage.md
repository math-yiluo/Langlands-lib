# Actual special-fibre images under local coefficient extension

This internal derived unit compares actual schematic images after a local
extension of integral coefficients, and specializes the result to the
maximal-unramified extension. All declarations use arbitrary universe `u`.

For affine groups over a field, `SchematicImage.isoOfIsoSquare` constructs
the isomorphism of actual image groups induced by an isomorphic source and
target square `f ≫ d.hom = e.hom ≫ f'`. The two closed schematically
dominant factorizations of this composite have the same all-test range.
The published dominant-factorization comparison supplies their actual
isomorphism. `isoOfIsoSquare_hom_comp` preserves the ambient target
isomorphism. `isParabolic_inclusion_of_isoSquare` transfers geometric
parabolicity through the source and ambient isomorphisms.

Let R and A be local domains with fraction fields K and L. Suppose the
coefficient algebras form the scalar towers required by
`IntegralModel.baseChange`, and the map R → A is local. For any compatible
map φ of actual integral models, `Hom.specialFibreImageBaseChangeIso`
identifies the residue extension of the original special-fibre image with
the actual image after coefficient extension. It composes the published
flat base-change comparison for schematic images with `isoOfIsoSquare`,
applied to the existing `Hom.specialFibreBaseChangeIso_naturality` square.
Its compatibility theorem follows from the two component comparisons and
retains the specified ambient `specialFibreBaseChangeIso`.

`Hom.isParabolic_specialFibreImage_of_baseChange` assumes the residue-field
extension is algebraic. It transports parabolicity of the upstairs actual
image through the inverse naturality square, then applies the published
algebraic-extension reflection theorem for schematic-image parabolicity.
No smoothness or connectedness of the integral models is required.
Parabolicity of the upstairs image remains an explicit input.

For a nonarchimedean local field F, `Hom.unramifiedSpecialFibreImageIso`
is the inverse of the general comparison with coefficients
`fixedFieldIntegers F` and fraction field `inertiaFixedField F`.
`Hom.isParabolic_specialFibreImage_of_unramified` applies the reflection
theorem to that extension. The proved `fixedFieldResidueIsAlgClosure`
supplies algebraicity of its actual residue extension. The proof identifies
the quotient-induced residue algebra with the algebra specified by
`residueToFixedField F`, by checking their maps on all residue classes.

Provenance is composition of the imported Library pullback comparisons,
dominant-factorization and parabolicity transport and reflection theorems.
This unit proves no facet-generation or reduction-preimage assertion and
does not prove `UnramifiedFacetParabolicImageStatement`.
