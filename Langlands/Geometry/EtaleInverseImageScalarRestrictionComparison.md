# Agreement with the existing etale-restriction scalar comparison

Let `f : Z ⟶ X` be etale, with `X`, `Z : Scheme.{u}`. Let
`φ : R →+* S` be any homomorphism of commutative rings in `Type u`.
Module carriers remain in universe `u`; no flatness or finiteness hypothesis
is imposed on `φ`. This internal construction identifies the general
inverse-image/scalar-extension comparison with the earlier
etale-restriction/scalar-extension comparison.

The imported `inverseImageIsoRestriction` identifies the actual constructed
inverse image with restriction along an etale map. The imported
`sheafExtendScalarsPullbackIso` was constructed from sheafification
compatibility in `EtaleScalarExtensionPullback`.
The imported `inverseImageExtendScalarsIso` was constructed from actual
composite adjunctions for arbitrary `f`.
Their agreement is proved here, rather than imposed as compatibility data.

## Normalizing the older comparison

`restrictionGeometricUnit_restrictScalars` proves that the unit of the
actual restriction/geometric-direct-image adjunction commutes with
restriction of coefficient scalars. The unit comes from the adjunction on
actual small-etale objects; its presheaf map is coefficient independent,
so the equality follows from equality of the underlying presheaf maps.

The private source adjunction composes scalar extension over `X` with
etale restriction, and the private target adjunction composes etale
restriction with scalar extension over `Z`. Their common right adjoint is
scalar restriction over `Z` followed by geometric direct image with
`R` coefficients. Its strict interchange is the same one used in the
general construction.

The private lemma `scalarRestrictionComparison_unit` proves that the older
sheafification comparison intertwines these two actual composite units.
It expands the composite units, uses the coefficient-independent geometric
unit just proved, and applies naturality of that unit to the scalar
extension unit. The existing proved
`sheafExtensionUnit_pullback` from `EtaleScalarExtensionPullback` then
identifies the final two maps. This is where the normalization of the
older sheafification construction is used.

Injectivity of the actual source Hom adjunction correspondence identifies
the older comparison with `Adjunction.leftAdjointUniq` for these two
composite adjunctions. The private helper
`conjugate_sameRightUniqueness`, proved from the Hom correspondence and
counit equation, therefore computes its conjugate as the identity on the
common right adjoint. Neither this unit equation nor the uniqueness
identification is assumed.

## Agreement with the general inverse image

`inverseImageExtendScalarsIso_restriction` is an equality of actual natural
transformations. One route applies the general scalar comparison and then
identifies the `R`-coefficient inverse image with restriction. The other
first identifies the `S`-coefficient inverse image with restriction and
then applies the older sheafification scalar comparison.

The proof applies injectivity of adjunction conjugation for the actual
composite scalar/geometric adjunctions. The conjugate of each
inverse-image/restriction comparison is the identity, since it was
constructed by uniqueness of left adjoints with the same geometric right
adjoint. The older scalar comparison has the identity conjugate computed
above. The general scalar comparison has the strict direct-image/scalar
interchange conjugate already proved in
`EtaleInverseImageScalarCoherence`. Whiskering and composition formulas
reduce the resulting diagram to identities.

`inverseImageExtendScalarsEtaleIso` transports the general scalar comparison
through the actual inverse-image/restriction isomorphisms on both sides.
`inverseImageExtendScalarsEtaleIso_eq` proves that this actual natural
isomorphism equals the older `sheafExtendScalarsPullbackIso`.
It follows from the preceding natural-transformation equation and
cancellation of the inverse-image/restriction isomorphism.

This establishes agreement of the two existing scalar-extension models on
their common etale scope. It does not construct the separate general
inverse-image/scalar-restriction comparison. No exactness of scalar
extension, cohomological coefficient-change theorem, support, equivariant
or Harris specialization is asserted.
