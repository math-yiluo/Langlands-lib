# Split reduced-norm-one groups over the original ground field

Authors: Worker 124.

For a finite-dimensional central simple algebra `A` over a field `K` and a
specified splitting chart `K ⊗[K] A ≃ M_d(K)`, where `d` is the actual reduced
degree, `CentralSimpleUnits.Splitting.groundIso` identifies the actual
reduced-norm-one group over `Spec K` with the published `SL_d` over the same
base. No extension of the base scheme occurs in this comparison.

The existing coefficient equivalence sends every norm-one tensor unit to its
matrix under the extended chart. Composing with `normOnePointsEquiv` gives
`groundPointsEquiv` on every relative test scheme, using its algebra of global
sections. The naturality proof applies the existing splitting-map naturality
to the section algebra map of an arbitrary test restriction. The two actual
point models therefore yield a group-scheme isomorphism by Yoneda.
`groundIso_hom_points` records its specified chart on all tests.

For the binary matrix algebra, the dimension is four and the reduced degree is
two. The canonical left-unit tensor equivalence supplies `binaryMatrixChart`;
`binaryMatrixNormOneIso` specializes the preceding construction to identify
its actual norm-one group with `SL₂`. All characteristics are permitted.

This is an internal derivation from the actual norm-one coefficient comparison,
the extended splitting chart, and the represented special-linear point model.
It provides an isomorphism and does not assert simple connectedness without a
separate theorem about one of these groups.
