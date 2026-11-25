# Actual special-fibre images under local coefficient extension

This module, internal and derived, compares actual schematic images after a local
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
This module proves no facet-generation or reduction-preimage assertion and
does not prove `UnramifiedFacetParabolicImageStatement`.

## Recovery and reverse-oriented squares

# Actual special-fibre images under model recovery

This internal construction transports actual schematic images through
commutative isomorphism squares and compatible integral-model isomorphisms,
and descends their parabolicity under coefficient extension. All constructions
retain arbitrary universe `u`.

For affine groups over one field and a square `e.hom ≫ g = f ≫ d.hom`
whose vertical maps are group isomorphisms, `SchematicImage.isoOfReverseIsoSquare`
identifies the actual schematic images. Its inclusion equation is
`imageIso.hom ≫ inclusion g = inclusion f ≫ d.hom`.
It follows that parabolicity of the inclusion of the image of `g` implies
parabolicity for the image of `f`. The proof compares two closed,
schematically dominant factorizations of the same homomorphism and then
transports the parabolic subgroup through the source and target isomorphisms.

For integral models over the same local domain with the same fraction field,
`Iso.specialFibreImageIso` applies this comparison to two extensions of the same
generic morphism and compatible source and target model isomorphisms inducing
the generic identities. Generic rigidity makes the model square commute;
residue base change gives the required special-fibre square.
`Iso.specialFibreImage_isParabolic` transports parabolicity through this square.

For a local coefficient extension of local domains, with compatible fraction
fields and an algebraic induced residue-field extension,
`Hom.specialFibreImage_isParabolic_of_baseChange` descends parabolicity from the
actual coefficient-extended model map. The special-fibre coefficient comparison
identifies that map with the residue extension of the original map. Flat-field
base change for actual schematic images and algebraic-extension descent for
parabolic subgroups then prove the claim. No finiteness assumption on the
residue extension is imposed.

For a nonarchimedean local field `F`,
`Hom.specialFibreImage_isParabolic_of_unramifiedModels` applies the preceding
results to an identity-generic map and any two supplied smooth models over the
actual maximal-unramified integers. Each supplied model must have exactly the
integral-point subgroup of the corresponding coefficient-extended original
smooth model. Smooth Hom extension constructs compatible model isomorphisms
from these equalities. The actual unramified residue field is an algebraic
closure of the original residue field; the induced integral residue algebra
is checked to equal the published residue map. Thus parabolicity for any
identity-generic map between the supplied models descends to the original map.
The final `RelativeComponentModelHom` wrapper applies this result to the actual
neutral map and yields `HasParabolicSpecialFibreImage`.

The provenance is a derived use of existing schematic-image factorization,
model rigidity, smooth model recovery and parabolic descent results. This module
assumes the specified models and integral-point equalities. It asserts neither
model existence nor the exact reduction-preimage equality nor the
opposite-factor theorem it serves.
