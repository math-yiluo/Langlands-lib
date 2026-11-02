# Cartesian relative spaces and points of their base changes

For an arbitrary morphism `f : X ⟶ S`, the published relative space of an
`S`-scheme `T` is the actual fibre product `T ×_S X`. The projection square
of every morphism in `Over S` is Cartesian. The proof cancels the
Cartesian square defining `T ×_S X` from the larger square defining the
source fibre product.

`relativeSpace_map_property` therefore transfers every morphism property
stable under base change from a slice map's underlying map to its actual
relative-space map. The module records the affine, flat, surjective and
quasi-compact specializations used in descent.

An arbitrary scheme map `a : V ⟶ T ×_S X` gives an `S`-structure on `V`.
`relativePointSection` is the map from `V` to `V ×_S X` whose first
projection is the identity and whose second projection is that of `a`.
Composing with the induced relative-space map recovers `a`. These are
actual scheme maps with their projection equations.

This is internal derived content from the published relative geometry,
categorical pullback cancellation, and Mathlib's base-change-stable
morphism properties. No rigidification, descent assertion or sheaf
condition is proved here.
