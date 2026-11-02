# Affine opens under affine change of the represented factor

This internal helper belongs to the scheme-representability proof for separated
commutative group algebraic spaces. It is derived from the imported Library
interfaces and Mathlib's representable morphism properties and scheme affineness;
it introduces no independent literature assertion.

`IsAffineMorphism f` means that the presheaf transformation `f` is representable
by schemes and that every projection in a represented scheme pullback is an
affine scheme morphism. It uses the relative morphism property induced by
`IsAffineHom` and the forgetful functor from schemes over the base. Both the
base and the source and target presheaves are arbitrary; no sheaf condition is
required.

`AffineOpenSubfunctors.IsAffineOpen.preimage_of_affine` proves that an affine
open subfunctor pulls back to an affine open along any representable affine map
of presheaves on schemes over a base. Choose an affine scheme representing the
original open and use relative representability of the affine map to construct
its scheme pullback. The projection to the original affine chart is affine, so
this new representing scheme is affine. The other projection is an open
immersion by base change. Its range is the inverse image of the original
subfunctor, and its factorization through that subfunctor is a componentwise
bijection, hence an isomorphism. Cancelling this isomorphism establishes the
open-immersion property of the subfunctor inclusion.

`AffineOpenSubfunctors.IsAffineOpen.preimage_mapRight` applies this to
`extProd.mapRight ρ`, the map `F × Y(Λ') → F × Y(Λ)` induced by a scheme map
`ρ : Λ' → Λ` over the base. Its sole extra hypothesis is that the underlying
scheme map of `ρ` is affine. The pullback square
`extProd.isPullback_mapRight ρ` identifies this map as a base change of `Y(ρ)`.
Scheme Yoneda carries `ρ` to a representable affine map, using represented scheme
pullbacks and stability of affine morphisms under base change. Neither the base
nor `Λ` is assumed affine, and no sheaf or group structure on `F` is required.
