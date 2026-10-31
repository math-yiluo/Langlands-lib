# A trivial rational tangent kernel forces cotangent surjectivity

The theorem
`Langlands.AlgebraicGeometry.tangentKernel_cotangentSurjectivity` proves the
unchanged published proposition
`Langlands.AlgebraicGeometry.TangentKernelCotangentSurjectivityStatement`.
For an arbitrary field, a morphism of schemes over that field, and a rational
point of the source, a trivial kernel on actual dual-number tangents implies
surjectivity of the actual stalk cotangent map. All schemes and the field
have the target's arbitrary universe `u`.

This is an internal derivation from the published stalk and dual-number
adapters and Mathlib linear duality, rather than a transcription of an
external proof. The imported statement and its dependencies are preserved.

The proof equips the source stalk at the rational point and the target stalk
at its image with the canonical base-field algebra structures. Write `r` for
the source's rational augmentation and `a` for the actual stalk algebra map
of the scheme morphism. The map in the conclusion is then exactly
`augmentationCotangentMap r a`.

Mathlib's `LinearMap.dualMap_injective_iff` reduces its surjectivity to
injectivity of the dual map. Since this is a linear map, it suffices to prove
that a functional `ell` annihilating the cotangent map vanishes.
`cotangentDualNumberLift r ell` constructs an augmented dual-number algebra
map, and `Picard.rationalStalkTangentMap` turns it into an actual scheme
tangent at the given rational point.

The annihilation equation identifies the composite of that lift with `a`
with the constant lift of `r.comp a`. Naturality of the stalk construction,
using `Picard.spec_stalkMapAlgHomOver_comp`, identifies the corresponding
scheme tangent with its postcomposition by the original scheme morphism.
The composite augmentation agrees with the canonical augmentation of the
image rational point by
`Picard.rationalStalkAugmentation_comp_stalkMapAlgHomOver`; composing its
spectrum with the target's stalk morphism recovers the image rational point.
Consequently the postcomposed tangent is constant.

The target's kernel hypothesis now makes the original tangent constant.
`Picard.rationalStalkTangentMap_eq_constant_iff` reflects this equality back
to the stalk lift, and `cotangentDualNumberLift_eq_constant_iff` gives
`ell = 0`, completing the duality argument.

The proof uses no finite-dimensionality, algebraic closure, finite-type,
properness, characteristic, smoothness, or reducedness assumption.
