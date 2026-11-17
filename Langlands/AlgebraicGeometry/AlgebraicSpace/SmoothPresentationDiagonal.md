# Diagonal geometry from a smooth scheme presentation

Worker 801.

This internal derived module uses published smooth-cover descent and
kernel-pair constructions. It introduces no new geometric axiom and
does not assume that the algebraic space is a scheme.

`relative_diagonal_of_smooth_presentation` takes an algebraic space `X`,
a smooth surjective map from a scheme `U`, and an actual represented
kernel pair `R` with endpoint maps `t,s`. A scheme morphism property `P`
of `(t,s) : R → U ×ₛ U` transfers to the diagonal of `X`, provided `P`
is stable under base change and descends along surjective flat locally
finitely presented morphisms. The product of the smooth presentation
with itself is a smooth surjective presentation of `X ×ₛ X`. The
published kernel-pair diagonal square and preservation of products by
the scheme Yoneda functor identify the base change of the diagonal
with `(t,s)`. The published
`ActionQuotientFiniteness.relative_of_isSmooth_isSurjective` then
descends `P`.

`smooth_atlas_of_smooth_presentation` assumes in addition that `U → S`
is smooth. For any etale chart `V → X`, form `W = U ×ₓ V`. Its map to
`U` is etale, so `W → S` is smooth; its map to `V` is smooth and
surjective. Smoothness descends along that map to give smoothness of
`V → S`.

`formallyUnramified_atlas_of_open_diagonal` assumes the space diagonal
is an open immersion. The kernel pair `E = V ×ₓ V` of an etale chart
has etale projections to `V`, and its map to `V ×ₛ V` is an open
immersion by base change of the space diagonal. The diagonal section
`V → E` is open because it is a section of an etale morphism. Their
composite is the diagonal of `V → S`, proving formal unramifiedness
of that structural map.

Finally, `etale_structural_atlas_of_smooth_presentation` chooses an
existing etale surjective chart of `X` and applies these two results.
Its structural morphism is smooth and formally unramified, hence
etale. The conclusion is an actual atlas with etale structure map,
expressed by `HasAtlasProperty (@Etale) X`. It includes no
representability assumption on `X → S`.

These lemmas hold over arbitrary scheme bases, in every universe,
without affine, Noetherian, quasi-compact or group hypotheses. Their
provenance is entirely the indicated existing Library results and
Mathlib's base-change, section and diagonal properties.
