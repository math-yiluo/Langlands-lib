# Closed extensions over enlarged finite S-integer rings

This internal construction derives closed arithmetic extensions from actual
integral-model homomorphisms and finite coefficient descent of closed
immersions. It uses the supplied generic homomorphism and canonical
coefficientwise S-integer inclusions. All objects lie in the arbitrary common
universe `u`.

`Hom.isClosedImmersion_generic` rewrites the generic pullback of the model
homomorphism as the supplied generic homomorphism conjugated by the two actual
generic-fibre isomorphisms. Thus the generic pullback is closed whenever the
supplied generic homomorphism is closed.

`enlargeHom` pulls an existing model homomorphism to the canonical finite
enlargement of its two models. `exists_enlarged_closedHom` finds a finite
enlargement where that same pulled-back homomorphism is a closed immersion.
It first spreads closedness to a finitely generated coefficient algebra using
`Descent.FiniteCoefficient.exists_fg_closed_baseChange`. It then embeds this
algebra into a finite S-integer ring containing the original base. Closed
immersions persist under this further pullback. Naturality of the actual
pullback comparisons identifies the canonical arithmetic map with that
iterated pullback, conjugated by the comparison isomorphisms. This proves the
closedness conclusion for the specified `enlargeHom` map.

`EnlargedClosedHomData` stores the finite set of places, its inclusion of the
original set, and closedness of this same `enlargeHom`. The definition
`enlargedClosedHomData` chooses these fields from the proved existence theorem;
it introduces no additional hypotheses beyond closedness of the supplied
generic map.

The construction presupposes an extending model homomorphism and asserts no
reductive, parabolic or connected fibre properties. Those remain obligations
of the full simultaneous spreading theorem.
