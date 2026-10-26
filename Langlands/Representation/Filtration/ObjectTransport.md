# Pullback and equivalence transport of actual object filtrations

This internal adapter packages existing invariant-subspace and quotient
constructions for a supplied `ObjectRepFiltration`. It supplies no existence
theorem for a composition series, segment filtration, or classification.

`ObjectRepFiltration.comp s f` pulls the action back along any monoid
homomorphism `f : H →* G`. Each step has exactly its original underlying
submodule; invariance follows by applying the original invariance to `f h`.
Monotonicity, the zero endpoint, and the full endpoint are inherited.
`compGradedEquiv` is the identity linear equivalence on the actual successive
quotient, with its pulled-back action. The coefficient ring is any commutative
ring. Surjectivity of `f` is unnecessary: the assertion concerns a supplied
filtration and does not assert preservation of simple factors.

Over a field, the published `LengthTwo.transport e s` applies to a filtration
of any length and is reused directly here.
Its steps are inverse images of the original steps under `e.symm`.
The membership theorem records that exact construction.
`equivTransportGradedEquiv` identifies an original graded quotient with the
corresponding transported graded quotient. The ambient intertwiner sends the
upper step onto the transported upper step and has precisely the original
lower step as the preimage of the transported lower step. The published
`LengthTwo.nonempty_gradedEquiv` therefore yields an actual equivariant
isomorphism, selected with `Classical.choice`.

All filtration lengths, including zero, are allowed. The group and both
representation carriers retain independent universes. The construction assumes
neither simplicity of the layers nor finite-dimensionality of any carrier.
Its provenance is internal: it reuses the published actual-filtration
definitions and the general transport and quotient-map lemmas in
`Filtration.LengthTwoMatching`. Despite that module's name, the reused
transport and quotient-map lemmas have no length-two hypothesis.
