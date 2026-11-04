# Localization of original compatible strong atlas maps

This internal construction applies Mathlib's categorical localization to
the existing `CompatibleAtlasPresentation` category and the actual
`quasiIsomorphisms` class of `CompatibleStrongQuasiIsomorphisms`. The
coefficient field is a complete ultrametric normed field, with trivial
valuation allowed. Original presentations have ambient universe `v`
and an independent chart-index universe `w`.

Objects are the original actual affinoid atlas presentations. Their maps
carry every admissible bounded algebra pullback and the explicit original
local-domain compatibility law of `CompatibleStrongMaps`. The inverted
maps satisfy the existing full `StrongHom.IsQuasiIso` condition on their
underlying strong maps: the ambient continuous map is a homeomorphism,
and every admissible chart pullback represents its relative image,
including unique bounded factorization over every presented affinoid test.

`LocalizedCategory` is Mathlib's path-and-relations construction for this
particular category and morphism property. Paths use original arrows and
formal inverses of full quasi-isomorphisms, and the quotient imposes the
identity, composition and two inverse relations. `localizationFunctor`
is the quotient functor with its `IsLocalization` instance.
`localizedObjectEquiv` identifies its objects with the original compatible
presentations and agrees with the object function of the quotient functor.
The morphism universe is the maximum of the original object and morphism
universes used by Mathlib's standard localization.

For an original full quasi-isomorphism, `localizedQuasiIso` constructs
an isomorphism between the corresponding quotient objects. Its forward
arrow is exactly the quotient image of the original map.
`localizedQuasiIso_hom_inv_id` and `localizedQuasiIso_inv_hom_id` prove
the two inverse equations in this quotient.

`descend` constructs a functor from the quotient for any original functor
that inverts the specified full quasi-isomorphisms.
`localizationFunctor_descend` proves strict equality of its composite
with the quotient functor and the original functor. `descend_unique`
uses Mathlib's uniqueness theorem to identify every other strict
factorization with this construction. `localizedFunctorEquivalence`
also supplies the universal property for natural transformations:
functors from the quotient form a category equivalent to the full
category of original functors inverting the specified class.

`spaceFunctor_inverts_quasiIsomorphisms` proves that the existing literal
ambient-space functor satisfies the required inversion premise. For each
specified map, its homeomorphism clause gives an isomorphism in `TopCat`
by `TopCat.isIso_iff_isHomeomorph`. Consequently
`localizedSpaceFunctor` is constructed by descent, and its composite with
the quotient functor is exactly the original `spaceFunctor`.
`localizedSpaceComparison` packages this equality as a natural
isomorphism. Its component at each original presentation is the identity
of that presentation's ambient space. The object and map recovery
equations retain the literal space and the original continuous map.

`localizedSpaceFunctor_map_quasiIso_inv` identifies the image of a formal
inverse with the continuous inverse of the original ambient
homeomorphism. The proof first identifies the image isomorphism by its
forward arrow, using the original map recovery, and then applies equality
of inverse arrows. `localizedSpaceFunctor_unique` proves uniqueness among
strict extensions of the literal space functor.

The provenance is internal, using the existing actual compatible
category, its proved full quasi-isomorphism property, and Mathlib's
constructed localization and universal property. This adapts the same
construction used in `SaturatedStrongLocalization` to the original
compatible category. It requires neither saturation nor directedness of
the original atlases. Comparison with the saturated localization,
identification with the full intended analytic-space category, analytic
etale and quasi-etale sites, equivariant constructions, compact and
distinguished domains, and Harris specializations remain subsequent
obligations.
