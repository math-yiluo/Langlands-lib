# Actual jet sections from ambient affine coordinates

Let `G` be an actual group scheme over any scheme `S` and let
`j : G → Spec B` be a supplied actual scheme morphism.
`coordinateMap` restricts each ambient function to the part of `G` over a
base open. `jetCoordinateMap` restricts the same function to the actual
identity-jet subscheme. Its restriction compatibility is the naturality
of pullback of functions, and `jetCoordinateMap_eq` identifies it with the
actual jet inclusion applied to `coordinateMap`.

`VanishesAtIdentity G j I` means that every function in an ambient ideal
`I` vanishes after pulling back along the actual composite from the identity
section to `Spec B`. This predicate concerns the actual morphism and its
actual global functions.

When `G → S` is affine, identity vanishing implies that coordinates from
`I` lie in each affine base open's augmentation kernel. Thus coordinates
from `I^(n+1)` vanish in the order-`n` augmentation quotient. The canonical
`sectionsRingEquiv` identifies this with vanishing on the actual jet
subscheme. The sheaf property then gives global vanishing; the base need
not be affine. `quotientCoordinates` therefore constructs an actual ring
homomorphism from `B/I^(n+1)` to global sections of the actual identity jet
module. Its representative formula records the ambient functions themselves.
`sectionsEquiv_restrict_quotientCoordinates` identifies the restrictions of
these global sections with the same functions' classes in every actual
affine augmentation quotient.

This is an internal functoriality and generator construction, derived from
pullback of functions, ideal powers, affine jet quotient comparisons and
the sheaf axiom. It makes no assertion that these generators are surjective,
that a particular parabolic inclusion supplies the identity-vanishing
condition, or that the resulting section quotient classifies a particular
Grassmannian point. Those require the corresponding geometric inputs.
