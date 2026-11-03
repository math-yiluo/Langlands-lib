# Descent of geometric connectedness along a surjective base change

The theorem `geometricallyConnectedSurjectiveDescent` proves the exact published
`GeometricallyConnectedSurjectiveDescentStatement` at every universe `u`.
For arbitrary scheme morphisms `f : X → S` and `g : Y → S`, surjectivity of `g`
and geometric connectedness of `X ×[S] Y → Y` imply geometric connectedness of `f`.
No flatness, finite presentation, smoothness, or openness assumption is needed.

The implementation reuses the published Library theorem
`AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective` from
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective`.
Its same-universe `DescendsAlong` assertion applies to the canonical pullback
through `MorphismProperty.of_pullback_snd_of_descendsAlong`. The arbitrary-square
wrapper applies `of_isPullback_of_descendsAlong` to the flipped square.
The exact target theorem introduces the two hypotheses and calls the canonical
wrapper. These wrappers add no hypotheses to the published descent theorem.

The reused Library theorem descends connectedness of each field-valued fiber by
choosing a point over the field and passing to its residue field; the resulting
surjective continuous map descends connectedness. Its implementation and original
port attribution remain in that imported Library module and its companion pair.
This module is an internal adapter of published mathematics for the
unipotent-radical quotient task. It asserts no quotient existence or affineness.
