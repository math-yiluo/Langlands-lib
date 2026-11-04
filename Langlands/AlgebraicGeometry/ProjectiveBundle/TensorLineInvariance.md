# Tensor-line invariance of actual projective frame bundles

Let `S : Scheme.{u}`, let `M` have the supplied fixed local rank `n + 1`,
and let `N` be a locally free rank-one module sheaf on `S`. The construction
uses the joint basis of opens carrying both an actual frame of `M` and an
actual trivialization of `N`. The source and tensor frame atlases use this
same basis and cover.

`chartFunctor_map_eq` proves equality of their actual scheme transition maps.
It unfolds a chart map as the projective dual-frame change followed by the
relative projective restriction. The arbitrary-overlap theorem
`LocalFrame.tensor_overlap_projectiveChange` identifies the first factors:
the unit from changing line trivializations acts trivially on projective space.
The restriction maps are definitionally identical.

`sourceCartesianAtlas` regards the source atlas's chart immersions as a
Cartesian atlas for the tensor cocycle. Compatibility follows from the
transition equality and the source cocycle's chart equation; its pullback
squares are the existing source chart pullback squares. The Cartesian-atlas
comparison therefore constructs `atlasIso`, an actual isomorphism from the
tensor atlas scheme to the source atlas scheme. `chart_atlasIso_hom`
identifies its restriction to every chart with the source chart map, and
`atlasIso_hom_toBase` proves that it is over `S`.

`frameBundleIso` composes the inverse comparison from the fixed tensor frame
bundle to its joint atlas, `atlasIso`, and the comparison from the source
atlas to its fixed frame bundle. Thus it is an actual scheme isomorphism
from `frameBundle (tensorObj M N)` to `frameBundle M`. The forward and inverse
structure-map identities prove that both directions lie over the original
scheme `S`. No additional global trivialization or atlas-comparison premise
is assumed.

This is derived internal infrastructure: the proof uses the established
arbitrary-overlap tensor-frame identity and the Cartesian-atlas gluing
comparison. It supplies scheme invariance under tensoring by a line bundle.
The degree-one line-bundle comparison, relative cubic embedding, and ordinary
moduli representability remain separate obligations.
