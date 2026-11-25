# Exact actual-image reduction preimages under unramified descent

This module, internal and derived, studies the reduction preimage of the rational
points of an actual schematic image, the subgroup in KP Axiom 4.1.22(4). It
transfers the equality of this preimage with the image of the source sections
through compatible model isomorphisms, and descends it from the actual
maximal-unramified coefficient extension. All declarations use an arbitrary
universe `u`.

## Rational points of an actual schematic image

For affine group schemes `A` and `B` over a field and a homomorphism `f`,
`SchematicImage.rationalImage f` is the range of the map on rational points
induced by the actual closed inclusion `SchematicImage.inclusion f`. It
contains every rational point of the image group, without assuming that the
source points surject onto them. The definition is irreducible, and
`rationalImage_def` gives its defining range. `mem_rationalImage` states that
membership means there is a point of `image f` mapping to the given point.

`map_mem_rationalImage` shows that the image of every source point lies in
this subgroup; the proof uses that the projection followed by the inclusion is
`f`. `map_mem_rationalImage_of_isoSquare` transports membership through a
square `e.hom ≫ g = f ≫ d.hom` whose vertical maps are group isomorphisms. It
maps the image point along the published reverse-square image isomorphism
`isoOfReverseIsoSquare`. `baseChangeSectionHom_mem_rationalImage` extends a
point of the image of `f` along a flat map of field spectra. The result lies
in the actual image of the base-changed homomorphism. The proof extends the
image point itself and applies the published flat base-change isomorphism of
schematic images. It does not lift the point through the original projection.

`square_mem_rationalImage` combines these results. Let `b`, `c`, `d` and `e`
form a commuting square `c ≫ b = e ≫ d`, where `b` and `e` have field spectra
as sources and `c` is a flat map of field spectra. Suppose the base change
along `b` of a section `x` of `C` lies in the actual image of the base change
of `f`. Then the base change of `x` along `d` and then `e` lies in the actual
image of the iterated base change of `f`. The published square comparison
isomorphisms and their section compatibility identify the two routes.

## Integral models

Let `R` be a local domain with fraction field `K`, and let `φ` be a map of
integral models `M → N` extending a generic homomorphism `f`.
`Hom.imageReductionPreimage φ` is the subgroup of target integral sections
whose reduction lies in `rationalImage` of the actual special-fibre map
`φ.specialFibreMap`. `Hom.sectionRange_le_imageReductionPreimage` proves that
the image of the source sections is contained in it, by reduction
naturality. `Hom.integralPointMap_identity` records that a model map
extending the identity preserves generic evaluation of sections.

`Iso.imageReductionPreimage_eq_range` assumes source and target model
isomorphisms `e` and `d` inducing the generic identities, and two maps `φ` and
`ψ` extending the same `f`. If the exact preimage of `ψ` equals the image of
its source sections, the same holds for `φ`. The proof transports a section of
the preimage of `φ` with `d`, applying `map_mem_rationalImage_of_isoSquare` to
the residue base change of the generic-rigidity square. It lifts the result
through `ψ` and returns along `e`. No smoothness, connectedness or residue
rational surjectivity is assumed.

Now let `A` be a local domain with fraction field `L`, with the scalar towers
used for coefficient extension and a local map `R → A`.
`Hom.baseChangeSection_mem_imageReductionPreimage` shows that the coefficient
extension of a section in the preimage of `φ` lies in the preimage of
`φ.baseChangeCoefficients A L`. The underlying `residueSquare_mem_rationalImage`
is `square_mem_rationalImage` applied to the published
`residueCoefficientSquare`. The residue-field extension is flat since it is a
field extension.

## Unramified descent

Let `F` be a nonarchimedean local field, `G` a group over `F`, and `φ` a
map `M → N` of integral models over the integers of `F` that extends the
identity of `G`. The three local instances name the published valuation
extension algebra, scalar tower and local homomorphism from these integers to
`fixedFieldIntegers F`.

`Hom.imageReductionPreimage_eq_range_of_unramified` assumes that the actual
unramified coefficient extension `φ.baseChangeUnramifiedId` has exact preimage
equal to the image of its source sections. It concludes the same for `φ`. Take
a target section `x` in the preimage of `φ`. Its coefficient extension lies in
the upstairs preimage and is therefore the image of an upstairs source section
`y`. By generic evaluation, `y` evaluates to the extension of the generic
point of `x`, so that point is integral for the extension of `M`. The published
`mem_integralPoints_rationalExtend_iff_unramified` descends this integrality
to an original source section `z`. Injectivity of generic evaluation on `N`
shows that `φ` maps `z` to `x`. This route does not use surjectivity of a
rational image projection over the original residue field.

`Hom.imageReductionPreimage_eq_range_of_unramifiedModels` supplies the upstairs
hypothesis from any two smooth models `Q` and `P` over `fixedFieldIntegers F`.
It assumes `M` and `N` smooth. Their coefficient extensions must have exactly
the integral-point subgroups of `Q` and `P`. Finally, some map `ψ : Q → P`
extending the identity must have exact preimage equal to its source-section
image. The published `unramifiedIsoOfIntegralPointsEq` gives compatible model
isomorphisms, and `Iso.imageReductionPreimage_eq_range` transfers the equality
before descent.

`RelativeComponentModelHom.hasParabolicReductionPreimage_of_unramifiedModels`
applies this to the neutral map of a relative component model morphism, using
the `neutral_smooth` fields of the source and target data. Unfolding the
definitions of `Hom.imageReductionPreimage` and `rationalImage` gives exactly
`HasParabolicReductionPreimage`.

## Provenance and scope

The provenance is a derived composition of Library results on schematic-image
factorization, flat base change, coefficient squares, generic rigidity,
smooth model recovery and exact descent of unramified integrality. The module
retains as explicit inputs the models `Q` and `P`, their smoothness, the
integral-point equalities and the upstairs map with its preimage equality. It
asserts no model existence and no parabolicity of special-fibre images. It
does not prove `UnramifiedFixedDepthZeroOppositeStatement`.
