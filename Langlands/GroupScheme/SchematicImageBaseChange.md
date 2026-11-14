# Actual schematic images and flat field base change

This is a derived construction for actual affine group schemes over fields.
It uses the existing schematic image, flat preservation of quasi-compact
schematically dominant homomorphisms, and uniqueness of closed dominant
factorizations. The parabolicity corollary uses the existing reflection theorem
for closed subgroup inclusions under algebraic field extension. No new claim is
attributed to external literature.

Let `f : G ⟶ H` be a homomorphism of affine group schemes over a field `k`.
Let `b : Spec L ⟶ Spec k` be an actual flat morphism for a second field `L`.
There are no smoothness, connectedness, finite-type or perfect-field assumptions.
The two affine structural morphisms ensure quasi-compactness of the relevant
homomorphisms.

`baseChangeIso f b` is an isomorphism from the actual base change of
`SchematicImage.image f` to
`SchematicImage.image ((GroupScheme.baseChange b).map f)`.
The proof compares two factorizations of the same pulled-back homomorphism:
the pulled-back original projection followed by the pulled-back original
inclusion, and the canonical projection followed by the canonical inclusion
of the pulled-back homomorphism. Flat base change preserves the first
projection's schematic dominance; both inclusions are closed. Thus
`isoOfDominantFactorizations` constructs the comparison.

`baseChangeIso_hom_comp` proves compatibility with the original inclusions.
Cancellation with the second closed inclusion then proves
`projection_baseChangeIso_hom`, compatibility with the two projections.
`baseChange_range_inclusion` identifies the entire subgroup functor after
base change with the range of the pulled-back homomorphism's schematic-image
inclusion. This is an all-test-scheme statement, and does not assert that an
image projection is surjective on rational points.

For an algebraic extension `L/k`,
`isParabolic_inclusion_of_baseChange` assumes parabolicity of the schematic
image of the pulled-back homomorphism. The comparison isomorphism first gives
parabolicity of the pulled-back original image inclusion. The existing
algebraic-extension reflection theorem then gives parabolicity of the
original image inclusion, which is already closed by construction.

These results perform image comparison and transport only. They do not prove
parabolicity of facet-model images over a splitting field or the final
`UnramifiedFacetParabolicImageStatement`.

The name `baseChange_range_inclusion` distinguishes this equality from
`range_inclusion_baseChange` in [SchematicImageFunctoriality](SchematicImageFunctoriality.md),
which has a different telescope and the opposite equality orientation.
