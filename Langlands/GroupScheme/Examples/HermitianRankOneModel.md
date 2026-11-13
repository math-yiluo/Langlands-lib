# Actual rank-one Hermitian models from attained matrix presentations

This internal construction combines the finite-source rank-one Gram
coordinates with the actual all-test scheme comparison. The fields `k` and `L`
share an arbitrary universe, and `L/k` is separable quadratic. There is no
characteristic restriction. The finite source index type lies in `Type` and
has cardinality `n + 1`, with `n ≥ 1`.

`RankOneModel k L n G` is a dependent tuple storing a diagonal Hermitian form on `Fin (n - 1)`,
units for its weights with their exact value equations, anisotropy of the
middle form, and an actual group-scheme isomorphism from `G` to the existing
`HermitianRoot.SchemeModel.groupScheme` for those same data.

The construction requires a supplied nondegenerate Hermitian pairing on the
source coordinate space, linear in the first argument and conjugate-linear
in the second. Its full value is `bar(t) dot J*z` for a supplied matrix `J`.
An actual totally isotropic submodule must have dimension one in `ENat`,
and every totally isotropic submodule must have dimension at most one.
Total isotropy uses vanishing on every ordered pair of elements.

The other input is an injective monoid homomorphism from the point group of
`G` to the actual general-linear group over the tensor coefficient ring for
every test scheme. Its range must be exactly the determinant-one full
`J`-isometry matrices, and it must commute with every test restriction. These
are supplied hypotheses. No affineness or finite type assumption on `G` is
needed for this conditional construction.

`nonempty_rankOneModel_of_attained_presentation` applies
`exists_rankOne_finiteSource_gram_coordinates` to obtain the diagonal
anisotropic middle, unit weights, a linear coordinate equivalence and
two-sided inverse rectangular coordinate matrices with the full Gram
congruence. It passes exactly these matrices, their identities and the
supplied raw point presentation to `isoOfFinitePresentation`. That
construction gives the actual group-scheme isomorphism. The definition
`rankOneModelOfAttainedPresentation` chooses the resulting model data.

The provenance is internal composition of the imported coordinate and
all-test comparison constructions, with classical choice only to choose
the concrete data. This module does not construct the separable quadratic
field or the matrix presentation from a Tits index, construct a
sesquilinear form from an arbitrary matrix, or establish the split-rank
comparison. In particular it does not prove
`OuterTypeARankOneHermitianStatement`.
