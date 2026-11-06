# Actual component equivalences and field-tower compatibility

Author: Worker 1107.

This is an internal derived construction from the published
`AlgebraicallyClosedComponentBaseChangeProof`,
`AlgebraicallyClosedComponents`, and `GaloisPointTowerBaseChange` interfaces.
It introduces no external structural assertion. All fields are in an arbitrary
common universe, and characteristic is unrestricted.

For a smooth affine group scheme `H` over an algebraically closed field `k`
and an explicit homomorphism `φ : k →+* L` to an algebraically closed field,
`allComponentBaseChangeEquiv H φ` packages the published extension
homomorphism and its published bijectivity as a group equivalence. Its forward
map is exactly `allComponentBaseChange H φ`. Its inverse is the continuous
map on connected components of the actual pullback projection, as proved by
`allComponentBaseChangeEquiv_symm_apply`. Surjectivity of the equivalence
reduces this formula to the published projection left-inverse equation.
`allComponentProjection` exposes that actual projection as a group
homomorphism. Neither algebraicity, separability nor finite dimensionality is
assumed for the extension.

`allComponentIso` sends an actual group-scheme isomorphism over an algebraically
closed field to a group equivalence on all actual connected components. Its
inverse is the map induced by the inverse isomorphism; the two inverse laws
follow from the published component-map composition and identity laws.
`allComponentBaseChangeEquiv_naturality` restates the published naturality
equation for the new equivalences and actual group-scheme homomorphisms.

For an actual tower `k → L → M` of algebraically closed fields, with the
explicit algebra structures and scalar-tower compatibility,
`allComponentIso_tower_projection` proves that the standard scheme pullback
comparison commutes with projection on all actual components. A representative
scheme point reduces this equation to
`towerBaseChangeIso_hom_fst`. Then
`allComponentBaseChangeEquiv_tower` identifies successive extension with direct
extension through that comparison. Injectivity of the direct projection on
components reduces the proof to the projection equation and the published
extension/projection inverse laws.

The carriers remain all connected components of the actual underlying
schemes. These constructions provide comparisons for specified field maps and
towers. A chosen geometric component group with its absolute Galois action,
comparison between unrelated algebraic closures, a component-group scheme,
and effective descent of fixed components to rational points remain separate
obligations. Different embeddings of an algebraic closure must be tracked;
no identification independent of all embedding choices is asserted here.
