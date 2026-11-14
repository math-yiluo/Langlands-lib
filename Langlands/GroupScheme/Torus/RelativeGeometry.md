# Geometry and closed normalizers of relative tori

This internal bridge uses the published definition `RelativeTorus.IsTorus`: an
actual group scheme becomes a finite split torus after an étale covering of its
base. The base scheme is arbitrary, the finite rank can vary across the cover,
and there is no reductivity or maximality hypothesis.

`RelativeTorus.IsTorus.smooth` proves smoothness of the structure morphism. On the
splitting cover, use `IsSplitTorus.smooth`, and descend through the fppf cover
obtained from that étale cover. The published fppf locality theorem and Mathlib's
flat descent instances supply this descent.

`RelativeTorus.IsTorus.geometricallyConnected` proves that the structure morphism
has connected fibres after every field-valued base change. A split torus stays
split after base change to a field and is connected by
`IsSplitTorus.connectedSpace`. Geometric connectedness is Zariski local on the
target, stable under base change, and descends along surjective base change by
`GeometricallyConnected.descendsAlong_surjective`. The same fppf covering argument
therefore descends this property from the splitting cover.

`RelativeTorus.closedNormalizer` applies the published
`smoothConnectedNormalizer` theorem to these two properties. For a closed
relative torus in a smooth affine group over any scheme, it supplies a closed
subgroup representing the actual `torusNormalizer` functor, with inclusion
locally of finite presentation. This conclusion concerns the all-test normalizer
of the torus range. It asserts neither smoothness of that normalizer nor
existence or finiteness of a Weyl quotient.

`RelativeTorus.normalizerGroupScheme` and `RelativeTorus.normalizerHom` choose
one such representative and its inclusion using classical choice.
`RelativeTorus.normalizerHom_spec` records exactly its three defining
properties: closedness, local finite presentation of the inclusion, and
representation of the actual normalizer on every test scheme.

The module is derived from the imported Library results, rather than a new
translation of a literature statement. It is a helper for the proof of
`WeylGroupSchemeFiniteEtaleStatement`. The normalizer input is the already
published proof of the subgroup case of Conrad, *Reductive group schemes*
(2014), Proposition 2.1.6; all geometric descent and split-torus inputs are
identified above by their Lean names.
