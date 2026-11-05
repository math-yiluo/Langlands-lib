# Homomorphisms and commutativity for affine group-scheme Weil restriction

This module continues `Langlands.GroupScheme.AffineWeilRestriction` over
commutative rings `A` and `B` in the same arbitrary universe, with `B` finite
projective over `A`. Input group schemes are actual groups in `Over (Spec B)`,
with affine underlying schemes and locally finite-type structural morphisms.
No smoothness, reductivity, splitness or finite-presentation hypothesis is used.

The construction is internal: it specializes the published
`GroupScheme.Corepresented.groupSchemeMap` to the tensor-valued point functors
already constructed in `AffineWeilRestriction`. Commutativity is derived from
the original commutative group object's point groups. No additional theorem
from external literature is assumed.

`pointTransformation` applies an input group-scheme homomorphism `f : G ⟶ H`
to actual points with coefficients in `B ⊗[A] T`. Its naturality is the existing
commutation of coefficient extension and postcomposition. The definition `map`
then uses the corepresented adapter to produce an actual homomorphism
`groupScheme A B G ⟶ groupScheme A B H`.

`map_affinePoints` states that, under `pointsEquiv` on both sides, this
homomorphism acts by the original `G.affinePointsTarget f` on every affine test
algebra. Thus its point action uses the original group-scheme homomorphism.
`hom_ext` detects equality by affine points, taking the identity point of the
source's own representing spectrum. `map_id` and `map_comp` apply this detection
and the injective multiplicative point equivalences to prove identity and
composition laws.

If `G.X` is a commutative group object, `groupScheme_isCommMonObj` proves that the
same restricted group object is commutative. For every relative test scheme,
the existing `Corepresented.pointsEquiv` identifies its point group with the
original commutative group's tensor-valued points on relative global sections.
Injectivity and multiplicativity reduce commutativity to the original point
group's `mul_comm`. The package `commGroupScheme` adds only this commutativity
proof: `commGroupScheme_toGrp` is a definitional equality. Consequently the
scheme, its geometric properties, its actual point groups, and the exact
canonical comparison `pointsEquiv` all remain those already constructed.

The continuous base-point comparison is supplied in a separate module. This
module makes no assertion about preservation of smoothness or reductivity or
about a restriction-of-scalars adjunction on arbitrary test schemes.
