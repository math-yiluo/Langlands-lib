# Identity-component geometry over fields without affineness

This derived helper establishes the geometry of a smooth field group's identity
component without assuming that the group is affine. It also supplies
irreducibility of residue-fibre identity components before openness of their
total relative union has been proved.

Smoothness makes the ambient field scheme locally Noetherian.
`fieldIdentityOver` is the actual open connected-component scheme at its unit,
using `componentScheme` and `componentι` from
`LocallyNoetherianComponentSchemes`. It carries the composite structure map to
the field spectrum. `fieldIdentityInclusion` is that actual inclusion over the
field. The component-open image formula identifies its range with
`IdentityComponent.identitySet H`.

The connected-component scheme is connected. Its structure map is smooth by
composition of an open immersion with the smooth ambient map. The generic smooth
connected field-scheme results in `OpenGeometry` give its integrality and
irreducibility. Taking the continuous image along the inclusion gives
`isIrreducible_identitySet`.

The unit section lands in its own connected component and hence factors through
the open inclusion. The resulting `fieldIdentityOne` is a rational section.
The smooth connected pointed field-scheme theorem therefore gives geometric
connectedness of this raw restriction. No group law on the restriction is
assumed or constructed in this helper.

Finally smoothness is preserved by the actual residue-field pullback.
Applying the field result to `residueFiber G s` proves
`isIrreducible_residueIdentitySet`, with no hypothesis that the relative
identity set is open. There is no affineness or quasi-compactness hypothesis.

The provenance is internal derivation from the published actual component
schemes, smooth connected integrality and pointed geometric connectedness,
the unit-point formula, and Mathlib's smoothness under base change and
irreducibility of continuous images. This helper does not prove relative
openness or the unconditional smooth structure statement.
