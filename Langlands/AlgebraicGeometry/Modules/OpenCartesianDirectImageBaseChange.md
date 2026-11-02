# Cartesian direct-image base change over an open immersion

This derived helper constructs `DerivedSections.openCartesianBaseChangeIso` for a
Cartesian square with bottom arrow `b : S′ → S`, top arrow `p : X′ → X`, and
vertical arrows `f : X → S` and `f′ : X′ → S′`. Both horizontal arrows are open
immersions. For every module sheaf `M` on `X`, its homomorphism is exactly the
specified `pushforwardBaseChange b f f′ p h.w M`. There are no quasi-coherence,
finiteness or flatness assumptions on `M` or the vertical arrows.

The auxiliary `restrictionCartesianBaseChange` is the adjunct, under restriction
along `b`, of the pushforward of the restriction unit along `p`, followed by the
commuting-square pushforward isomorphism. The Cartesian image/preimage identity
shows that every open `f⁻¹(b(U))` lies in the image of `p`. Consequently the
restriction unit is invertible on these opens. After restricting to `S′`, its
pushforward is therefore an isomorphism, as is the restriction adjunction's
counit. This proves that `restrictionCartesianBaseChange` is invertible.

`pushforwardBaseChange_eq_restrictionCartesianBaseChange` compares this adjunct
with the actual pullback-based comparison. The restriction-to-pullback
isomorphisms arise from uniqueness of left adjoints to the same pushforward.
Their unit identity and naturality of the square pushforward isomorphism identify
the two adjuncts. It follows that the specified pullback-based comparison is
invertible. `openCartesianBaseChangeIso` packages precisely that morphism using
`asIso`.

The provenance is internal and derived: the proof uses Mathlib's Cartesian
open-immersion image/preimage identity, restriction adjunction and uniqueness of
left adjoints, together with the Library's actual `pushforwardBaseChange` and
`pushforwardSquareIso`. The companion `OpenDirectImageBaseChange` gives the
special case of a chosen inverse-image open; this module permits any supplied
Cartesian square of open immersions. It is a helper for the cubic direct-image
task and does not assert arbitrary base-change invertibility or the prescribed
rank without the remaining affine-data and globalization arguments.
