# Invariance of actual components under algebraically closed field extension

Author: Worker 1604.

`algebraicallyClosedComponentBaseChange` proves the exact published proposition
`Langlands.GroupScheme.IdentityComponent.AlgebraicallyClosedComponentBaseChangeStatement.{u}`.
The fields, characteristic, universe and explicit homomorphism have exactly the
scope of that proposition, with no additional assumptions.

The proof uses the published geometric irreducibility theorem
`GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed` on `Spec L → Spec k`.
Its source is irreducible because `L` is a field. The published implication
`GeometricallyIrreducible.geometricallyConnected` then makes this morphism
geometrically connected. Base change gives geometric connectedness of the
actual pullback projection to `H`. Every morphism to the spectrum of a field
is universally open, so this projection is open. Mathlib's
`Scheme.Hom.connectedComponentsHomeomorph` identifies its map on components
with a homeomorphism. The helper
`componentProjection_injective_of_isAlgClosed` records the resulting
injectivity; it needs no smoothness, affineness or algebraic closedness of `L`.

The published `allComponentBaseChange_fst` says that this projection on
components is a left inverse of the specific homomorphism
`allComponentBaseChange H φ`. Injectivity of the projection makes it a right
inverse as well: the preimage of a component `c` is its actual projection to
`H`, and applying the projection to the desired equation reduces it to
`allComponentBaseChange_fst`. Combining this surjectivity with the published
`allComponentBaseChange_injective` proves the target.

This is a derived proof from existing Library theorems and Mathlib, using a
stronger geometric input than the rational-point route described in the
statement's Markdown. No new geometric-connectedness premise is introduced.
The imported geometric irreducibility theorem is the published port from the
Anthropic FLT formalization, identified in its paired Markdown and attribution;
its proof handles arbitrary field extensions through finite subalgebras and
injectivity of tensoring over a field. No source or target pair is modified.
