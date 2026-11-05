# Base change of the actual components selected by a section

This internal unit compares connected components in actual residue fibres.
Its sole finiteness assumption is that the original morphism is locally of
finite type. No flatness, smoothness, reducedness, quasi-compactness or
separation assumption is needed for these comparisons.

For a locally Noetherian scheme over a field, with an actual rational section,
`preimage_connectedComponent_of_field_isPullback` proves that the inverse
image of its selected connected component under an arbitrary field extension
is the connected component of any point above the selected rational point.
The selected component is an actual open subscheme and is geometrically
connected by `geometricallyConnected_connectedComponentOpen`. Pulling this
open subscheme back gives a connected scheme. The range of its inclusion is
exactly the inverse image of the old component. That inverse image is
therefore connected, contains the selected point, and equals its connected
component; continuity supplies the reverse inclusion.

For a Cartesian square of arbitrary schemes whose two sections commute,
`preimage_fiberComponent_of_isPullback` applies this field comparison to
Mathlib's actual Cartesian residue-fibre square. The original residue fibre
is locally Noetherian because it is locally of finite type over a field.
The published `fiberMap_fiberPoint` identifies the selected points.
`preimage_componentSet_of_isPullback_locallyOfFiniteType` then proves equality
of the inverse image of the original relative union with the new relative
union. Every point is represented in its actual residue fibre, where the
preceding component equality applies.

`fiberComponentBaseChangeIso` is an actual scheme isomorphism from the new
selected open component to the pullback of the original selected open
component along the residue-fibre map. Both maps into the new fibre are open
immersions with the same range, so the universal property of open immersions
constructs the isomorphism. The definition explicitly assumes local finite
type for both structure maps to make both selected open components available.
`fiberComponentBaseChangeIso_hom_snd` records compatibility with the actual
inclusion into the new residue fibre.

The construction derives internally from `SectionComponentFunctoriality`,
Mathlib's Cartesian residue-fibre square and open immersion range and lifting
theorems, and the companion `PointedConnectedComponentGeometry` development
by Workers 1480 and 513. It supplies a base-change input for the assigned
EGA section-component openness proof; it does not prove relative openness.
