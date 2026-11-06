# Reductivity detected by actual proportional-root centralizers

For a smooth affine field group `G`, an actual split-torus map
`i : T → G`, and a nonzero character `α`, the namespace
`RankOneCentralizerDetection` constructs an actual cocharacter,
its dynamic centralizer `groupScheme`, the closed `inclusion`
into `G`, and the canonical `torusHom` factoring `i`.
No reductivity hypothesis is used in these constructions.

The cocharacter is the existing generic kernel cocharacter
for `α` and the finite set of actual ambient roots. It pairs
to zero with `α`, and every ambient root pairing to zero with
it is integrally linearly dependent with `α`. The published
root comparison for actual dynamic centralizers therefore
proves that all roots in the constructed centralizer are
pairwise linearly dependent. The centralizer is affine and
smooth; it is connected when `G` is connected. A closed `i`
gives a closed torus factor, whose composite with the
specified inclusion recovers exactly `i`.

Over an algebraically closed field, suppose further that
`i` is closed and its existing all-test centralizer is its
range. If the constructed centralizer for every actual
ambient root has trivial unipotent radical, then `G` has
trivial unipotent radical. In particular, for connected `G`,
connected reductivity of those actual centralizers implies
connected reductivity of `G`. The hypothesis concerns only
the finitely many ambient roots. It does not assume
reductivity of `G`, reducedness of its root support or any
bound on the individual weight dimensions.

The implemented proof considers an arbitrary smooth connected
unipotent normal closed subgroup `j : H → G`. Its actual
normalized-conjugation action by `T` decomposes `Lie(H)`
into character weights. The file first proves that the
specified differential of `j` intertwines this action with
the ambient adjoint action, so every such weight maps into
the corresponding actual ambient weight.

For a nonzero weight with nonzero image, its character is an
ambient root. Its generic kernel cocharacter places that
infinitesimal point in the constructed actual centralizer.
`NormalUnipotentCentralizer` makes the intersection with `H`
trivial because this centralizer has trivial radical.
For weight zero, choose the published cocharacter whose
whole all-test centralizer equals the centralizer of `T`.
By the self-centralizer hypothesis this is represented by
`T` itself, whose radical is trivial. The same intersection
argument kills the zero weight.

Injectivity of the differential of `j` now kills every
weight in `Lie(H)`. Their internal direct sum spans the
whole actual Lie module, so that module is zero. Smooth
connected tangent subgroup equality then makes the
identity section of `H` an isomorphism. Its image through
`j` is therefore the bottom subgroup on every test scheme.
This proves exactly the existing ground-field radical
predicate. The published algebraically closed
pseudo-reductive comparison gives the final reductivity
conclusion.

The provenance is internal: this combines the published
generic cocharacter and dynamic centralizer constructions,
actual root and differential comparisons, torus-action
weight decomposition, tangent subgroup equality and
algebraically closed radical comparison with the actual
normal-unipotent intersection lemma. It implements the
reduction needed before proving the rank-one field cases.
Those cases, the required relative constructions and
openness of the unchanged reductivity locus remain
separate obligations.
