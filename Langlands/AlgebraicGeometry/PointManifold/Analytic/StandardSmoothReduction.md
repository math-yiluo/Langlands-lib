# Assemble analytic affine atlases from standard-smooth charts

`RegularAtlas.ofStandardSmooth` assumes a pointwise regular analytic chart
construction for every affine coordinate algebra that is standard smooth in
relative dimension `d`. For every affine scheme smooth of relative dimension
`d`, it then constructs a covering regular analytic atlas on actual points.

For each actual point, the published algebraic
`General.standardSmoothPrincipalNeighborhood` gives a principal open with
standard-smooth coordinate algebra containing its closed-point image. The
actual point factors through that open by the published local-ring point
criterion and `openPointLift`. The input chart covers this factor point;
`RegularChart.ofBasicOpen` transfers it to the original point space, where
the point inclusion identity proves source membership. Choice selects the
chart at each point. Empty carriers and dimension zero are included.

This is an internal adaptation by Worker 115 of Workers 135 and 1650's
published `PointManifold.General.StandardSmoothReduction`. The algebraic
neighborhood theorem is imported unchanged; only the analytic chart interface
is changed. The pointwise standard-smooth input is discharged in
`SmoothAffineManifold`.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
