# Actual GL simple roots and rational-point Aubert indices

This internal adapter uses the published general rational-point family and the
published GL root and block comparisons. It identifies ordered block shapes
with finite subsets of the actual simple relative roots of the diagonal torus,
for any field `k` and natural rank `N`. The definitions and proofs are in
`Langlands.Aubert.General.RationalPointFamily.GL`.

The cocharacter `ν` has strictly decreasing integer coordinates. The explicit
`upperCocharacter k N` has weights `a ↦ -a.val`; its strict decrease and
genericity are proved, including ranks zero and one. Thus the retained chamber
condition has an actual witness in every rank.

`edgeSimpleRootEquiv` sends each interior edge to the adjacent character
`e_a - e_(a+1)`, with its membership proof in the published simple relative
roots. Injectivity and surjectivity use the existing
`GroupScheme.GeneralLinear.simpleRootCharacter_injective` and
`simpleRelativeRoots_diagonalTorus`. The equivalence is between actual roots
and edges, rather than a newly introduced set of root labels.

`blockRootSubsetEquiv` composes the existing
`GeneralLinear.BlockShape.leviRootSubsetEquiv` with this equivalence on finite
sets. Its value is the image of the uncut edges. Its `rootSet` is exactly
`GroupScheme.GeneralLinear.blockSimpleRoots k B`, and its cardinality is
`N - B.length`. Consequently the general unadjusted coefficient
`(-1)^|I|` is the existing GL coefficient `(-1)^(N-B.length)`. The same
definitions retain the unique empty root subset in rank zero.

The three subgroup equalities compare the actual
`RationalPointFamily.parabolic`, `levi` and `unipotent` at this index to
the inverse images of the existing matrix subgroups. Their map is the
published `GroupScheme.GeneralLinear.rationalPointsEquiv`, with the canonical
global-section coefficient comparison. The proofs rewrite the root set, use
the published all-test standard subgroup equalities, and apply the published
canonical point comap formulas. They construct no replacement point group.

The provenance is derived interface assembly. The mathematical inputs and their
original-source correspondence are documented in the imported pairs
`GroupScheme.Rational.GeneralLinearIndexing`,
`GroupScheme.Rational.GeneralLinearStandardParabolicProof`,
`GroupScheme.Rational.GeneralLinearCanonicalPointsProof` and
`GroupScheme.Rational.GeneralLinearGenericCentralizer`. The existing
`Aubert.RootSubsetExpansion` supplies the GL block-root equivalence and
the block sign convention. No additional original-literature reading is
claimed here.

This adapter supplies indexing and algebraic subgroup comparisons. The full
Family 5 bridge still needs natural comparisons of normalized induction and
Jacquet functors, and the resulting equality of the rational-point and matrix
operators under the canonical continuous group comparison. No such equality
or completion of the general Aubert program follows from this module alone.
