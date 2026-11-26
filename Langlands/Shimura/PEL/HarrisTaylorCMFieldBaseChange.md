# Field base change of the represented Harris CM tower

`cmFieldOverTower` takes the existing represented normalized CM tower over
`Spec F` and pulls it back along `Spec K → Spec F` from the specified algebra
structure of the extension field `K`. It takes the exact existing
`CMRepresentabilityStatement` for the small levels and the same tensor,
Picard, polarization, finite Weil and adelic inputs as `representedCMOverTower`.
All fields and schemes are in universe zero, as in that tower.
`cmLocalOverTower` specializes `K` to `Global.FiniteCompletion F v` with its
canonical inclusion of `F`, where `v` is a finite place of the CM base field.
Harris identifies the CM field with the reflex field in his setting for
(4.3). The index of this construction is the given CM base field `F`
throughout.
The construction also admits a further complete field extension with its
composite `F`-algebra structure.

`cmFieldSchemeTower` forgets the structure map to `Spec K`.
`cmFieldProjection` is natural in every arrow of the existing small-level
transporter category. `cmFieldSchemeTower_isPullback` identifies each level
with its field pullback. For a transporter, the outer and lower squares
are these two level pullbacks and `Over.w` identifies the structure-map
composites. Cancelling the lower pullback proves
`cmFieldSchemeTower_map_isPullback`. This applies to the transition maps
and to both legs of the original Hecke correspondences. Smoothness of a level
follows from base change of its smooth represented structure morphism.

This is the algebraic field-base-change step on the Shimura-variety side
of Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), §4, printed pp. 308–309, especially (4.3). Harris uses a distinguished
split place and additional level conditions for the uniformization. The
underlying scheme base change, and the action of functorial pullback on its
level maps, apply to any field extension as here. The module constructs
the base-changed schemes and their maps. The analytic structure and the
uniformizing isomorphism are separate constructions.
Literature ID `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
