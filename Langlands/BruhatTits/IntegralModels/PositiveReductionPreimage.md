# Positive-subgroup containment and reduction preimages

This is derived infrastructure for the reduction-preimage part of
`UnramifiedFacetParabolicImageStatement`. Its provenance is the published
definitions of the actual reduction kernel and positive subgroups, existence of
reductive special-fibre quotients, and the reduction-preimage criteria in
`ReductionPreimage`. It asserts no new conclusion from external literature.
It does not prove facet-specific positive-subgroup containment, rational
surjectivity of an image projection, or parabolicity of the image.

All declarations are universe polymorphic. The coefficient ring is a local
commutative domain with the specified fraction field. The group scheme and
relative-component models are the actual objects used in `SpecialFibre`.
Such model data already carry smooth full and neutral models and connected
neutral fibres. The section-lifting results also assume the ring is Henselian.

For any supplied `SpecialFibreQuotientData Q`, even without its reductive-quotient
validity predicate, `congruenceKernel_le_positiveSections` follows because a
section in the reduction kernel reduces to the identity, which is a point of
the supplied radical subgroup. Mapping this containment to the generic fibre
proves `congruenceSubgroup_le_positivePoints`.

Given a model morphism with source indexed by the larger incident facet and
target by the smaller facet, containment of the target positive subgroup in
the source positive subgroup therefore puts the target congruence subgroup
inside the source integral-point image. This is
`congruenceSubgroup_le_integralPoints_of_positivePoints_le`; its proof also uses
the defining containment of source positive points in source integral points.
It does not require the models actually to be indexed by facets.

`hasParabolicReductionPreimage_of_positivePoints_le` combines that containment
with the two criteria in `ReductionPreimage`. Its explicit additional input
is surjectivity on original residue-field points of the canonical projection
onto the schematic image. Source smoothness is taken from the supplied model
data. The conclusion is the exact `HasParabolicReductionPreimage` equality of
subgroups of target integral sections.

Finally, `hasParabolicReductionPreimage_of_reductivePositivePoints_le` assumes
a perfect residue field and positive-subgroup containment for every pair of
valid reductive quotient data. It chooses such data using
`SpecialFibreQuotientData.exists_isReductiveQuotient` for each model and applies
the preceding result. This is the form needed to use the universally quantified
positive-radical clause; the image-projection surjectivity input remains explicit.

The construction `positiveReductionPreimageLift` applies the existing chosen
lift to the congruence containment derived from a supplied pair of positive
subgroups. Its specification proves that the original neutral-model map sends
the chosen source section to the specified target section. This is a function
choosing sections; no homomorphism law for the choice is asserted.

The theorem `SpecialFibreQuotientData.congruenceSubgroup_le_positivePoints`
is reused unchanged from [DepthZeroCompactOpen](DepthZeroCompactOpen.md).
