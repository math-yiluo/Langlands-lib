# Splitting the actual reduced-norm-one group

Authors: Worker 124.

This internal construction identifies the actual scalar extension of the
reduced-norm-one group of a finite-dimensional central simple algebra with
the actual special-linear group of its reduced degree. A splitting chart
over a field is supplied; no Galois, separability or characteristic
condition is imposed on that field extension.

The coefficient comparison uses the published extension of a splitting
chart to every commutative algebra over the splitting field. The actual
reduced norm is its determinant, so norm-one tensor units correspond to
all determinant-one matrices. The inverse comparison applies the inverse
algebra chart to the unit underlying a special-linear matrix.

The naturality of the chart matrix follows on pure tensors from the
compatibility of the coefficient map with the splitting field. The
actual base-change point comparison, followed by the actual norm-one
point comparison, supplies the prescribed matrix on every relative test
scheme. These comparisons commute with every test restriction.
Consequently the Library's point-model isomorphism constructs
`splittingIso`, an actual group-scheme isomorphism. Its formula on every
relative test is `splittingIso_hom_points`.

The construction derives from the published reduced norm, splitting
chart and relative point APIs; it is not a transcription of an external
theorem. It supplies a structural prerequisite for the quaternionic
spin-cover program. It does not prove simple connectedness of the
special-linear group or identify the binary quaternion action with a
spin cover.
