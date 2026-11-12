# Identifying the actual Hermitian group from all-test matrix points

This derived adapter turns a natural matrix description of all test points of a
group scheme into an isomorphism with the published weighted Hermitian group
scheme. It uses the actual tensor coefficient rings and their coefficient maps.

Fix a separable quadratic field extension `L/k`, with both fields in an arbitrary
common universe, a finite middle index in `Type`, and a diagonal Hermitian form
`H` with unit witnesses `w` for its weights. Let `G` be any group scheme over
`Spec k`. The input `e` gives a multiplicative equivalence, for every test scheme
`T` over `Spec k`, between `G`'s `T`-points and the determinant-one isometries of
`tensorForm k L H T`. Its naturality assumption says that precomposition with a
test morphism becomes entrywise matrix mapping by the actual `tensorMap`.
These hypotheses concern every test scheme, rather than just field-valued
points.

`matrixPoints_map` lifts the matrix naturality equation to the special unitary
subgroup by subtype and unit extensionality. The definition `isoOfMatrixPoints`
then applies the published `isoOfPointModels` to this natural description and
the actual Hermitian equalizer model's published `pointsEquiv` and
`pointsEquiv_map`. Its output is an isomorphism of group schemes over `Spec k`.
The theorems `isoOfMatrixPoints_hom` and `isoOfMatrixPoints_inv` prove its point
formulas in both directions. Finally `isoOfMatrixPoints_unique` proves that
every isomorphism realizing the given all-test equivalences is this one:
injectivity of the model point equivalence gives equality on every test point,
and `hom_ext_points` gives equality of the homomorphisms.

The provenance is internal Yoneda reconstruction from the published natural
matrix description of the actual Hermitian equalizer model. The adapter
requires no local-field condition, characteristic restriction, anisotropy,
affineness of `G`, or rank hypothesis. It does not construct the input natural
equivalences and does not classify an arbitrary group scheme. The local
rank-one classification still needs to produce the quadratic extension,
anisotropic form with its dimension bound, and the matrix equivalences (or
another actual group-scheme identification).
