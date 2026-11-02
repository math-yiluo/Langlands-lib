# The pair scheme of the tuple cross cover

This module constructs the pair scheme needed for changing from a higher tuple
tail to an invariant open of a lower tail. It is derived scheme-level
infrastructure for the symmetric-tuple filtration of the Stacks Project,
Lemma 68.8.6, Tag 07ST, and Lemma 68.8.3, Tag 0BBN. The registered originals are
`stacks-noetherian-approximation-2026-11-01` and
`stacks-stratification-2026-11-02`. The pair construction uses only the structural
maps of the already constructed relations and their actual scheme-valued
equivalence relation laws.

Work in arbitrary universe `u`. The original relation has separated source,
affine object and arrow schemes, and closed joint endpoint map. Fix `p ≤ q`
and a finite tuple bound `N`. Let `L` be the tail beginning at `p`, let `H` be
the tail beginning at `q`, and write `P` for the cross scheme with maps
`c : P → H.U`, `r : P → L.R`, and `v : P → L.U`.

`tupleTailCrossCoverPairScheme` is `B = P ×_{H.U} P`, with projections `a,b`.
`tupleTailCrossCoverPairArrow` is the morphism
`d = r(a) compose inverse(r(b)) : B → L.R`. The pullback condition for `B`
ensures composability. Its endpoint lemmas say that its target is `v(a)` and
its source is `v(b)`.

`tupleTailCrossCoverPair_hom_ext` proves that `d` and `b` jointly determine a
map into `B`. The map `a` is determined by its lower target, which is read
from `d`, and its higher source, which equals that of `b`.
`tupleTailCrossCoverPairArrow_isPullback` proves that the square with top
`d`, left `b`, right `L.s`, and bottom `v` is cartesian. Given an arrow `f`
of `L` and a cross arrow `z` with `s(f)=v(z)`, compose `f` with `r(z)` to
construct the first cross arrow. The two endpoint identities verify the
required lift; the preceding extensionality lemma proves uniqueness.

`tupleTailCrossCoverPairScheme_isAffine` uses affineness of the two cross
schemes and the higher-tail object scheme.
`tupleTailCrossCoverPairArrow_etale` is base change of the étale map `v`
along `L.s`.

`tupleTailCrossCoverPairImageOpen` is the inverse image under `L.s` of the
`q`th threshold open in `L.U`.
`tupleTailCrossCoverPairImageOpen_isCompact` uses quasi-compactness of `L.s`
(a morphism between affine schemes) and the established compactness of the
threshold. For `q < N+1`, `tupleTailCrossCoverPairArrow_range` identifies this
open with the full image of `d`: the forward implication uses the source
identity, and the reverse implication lifts a point through the cartesian
square using the known image of `v`.

This module does not construct a descended pair action or a Noetherian level.
