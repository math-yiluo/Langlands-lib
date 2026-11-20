# Actual identity jets under arbitrary change of base

Let `G/S` have separated structure morphism and let `b : T → S` be any
scheme morphism. This internal construction proves that the actual
closed identity neighborhoods and their actual module sheaves commute
with this base change.

The imported affine-local formula `IdealSheafData.ideal_comap_of_le`
identifies ideal-sheaf pullback with extension of ideals on sufficiently
small affine opens. Since extension commutes with powers,
`idealSheaf_comap_pow` proves this compatibility for every scheme map,
using a covering family of such affine opens.

The actual cartesian identity square identifies the pullback of the
original identity kernel with the new identity kernel: the identity is
a closed immersion because the group is separated over its base.
`ideal_baseChange` then identifies their actual jet ideals.
`baseChangeMap` is the resulting actual scheme map, and
`baseChange_isPullback` proves that the actual jet projection square is
cartesian.

`baseChangeIso` identifies the pullback of `IdentityJet.module G n`
with `IdentityJet.module G_T n`. It composes the existing actual affine
direct-image base-change isomorphism for the jet projection with the
actual pullback comparison for the structure module. The projection
is affine because its underlying map is a homeomorphism onto the base,
using the support of the identity jet. No flatness, smoothness, finite generation,
noetherian, or compactness assumption is made on the base or the map.
