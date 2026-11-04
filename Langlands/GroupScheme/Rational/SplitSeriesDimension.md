# Intrinsic dimension from a finite Ga-series

This internal adapter identifies the length of the existing `HasSplitSeries`
predicate with actual smooth relative dimension for affine connected group
schemes over every field in universe `u`. It imposes no characteristic,
perfectness or infinitude condition.

The length-zero case uses the natural zero-dimensional vector coordinates
constructed from all-test triviality. At a successor, the closed subgroup is
affine and connected, so induction identifies its smooth relative dimension
with its shorter series length. The quotient is the given one-dimensional
vector group. Its affineness and the source's affineness make the fppf map
quasi-compact. The published smooth-kernel quotient theorem identifies that
map's relative dimension with the kernel's. Composition with the
one-dimensional vector group's structure morphism gives the successor length.
Smoothness of the original group is a conclusion of this argument.

Uniqueness of smooth relative dimension on a nonempty scheme over a field
shows that all finite Ga-series on this group have the same length.
`IsSplitUnipotent.dimension` selects the length supplied by the existential
split-unipotence witness. The definition itself only requires the witness;
its geometric interpretation and independence from a chosen series use the
stated affineness and connectedness hypotheses. The selected dimension is
zero exactly when the group is trivial on every scheme test, so a nontrivial
group has positive selected dimension.

For an actual represented fppf quotient, with affine connected split-unipotent
kernel, source and target, the same smooth-kernel theorem and composition give
additivity of the three selected dimensions. If the kernel is nontrivial, the
target dimension is strictly smaller than the source dimension. The given
quotient is retained; the result neither constructs it nor assumes
surjectivity on the point group of every original test.

The provenance is internal: these are consequences of the published series
definition, zero coordinates, vector-group dimension, represented-kernel
smoothness and uniqueness and composition of smooth relative dimensions.
This provides dimension data for induction in the solvable maximal-torus
conjugacy task. Quotient existence, quotient splitness, stable-vector
existence, torus-action linearization and full conjugacy remain separate
obligations.
