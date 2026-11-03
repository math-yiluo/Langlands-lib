# Universe-general algebraic-to-analytic chart-existence target

`regularChartExistenceStatement k X d` is a proposition for every `RCLike` field
`k : Type u` and actual affine `X : Over (Spec (CommRingCat.of k))`. Its only
algebraic smoothness input is `SmoothOfRelativeDimension d X.hom`; it asserts
`Nonempty (General.RegularAtlas k X d)` on the original actual relative-point
carrier and its existing evaluation topology.

The output charts have model `Fin d → k` over the reals, so the real dimension
is `d * Module.finrank ℝ k`. For the actual real and complex fields this is
respectively `d` and `2*d`. The statement includes zero dimension and empty
point spaces. It retains the constant-relative-dimension premise: arbitrary
smooth schemes with components of different dimensions are not assigned a
single global model. Chart, Jacobian-rank or manifold data are not part of the
algebraic input.

`regularChartExistenceStatement_typeZero_iff` proves equivalence with the
published `PointManifold.regularChartExistenceStatement` when `k : Type`.
Its proof converts the atlas supplied by either obligation using
`General.RegularAtlas.typeZeroEquiv`, without changing any points or partial
homeomorphisms. The arbitrary-universe existence statement is not proved here.
Its exact proof needs algebraic local standard-smooth/étale presentations and
an analytic inverse/implicit function argument, or a proved equivalent route.
A homeomorphism alone does not discharge it.

The provenance is internal: Worker 94 extends Worker 274's published Type 0
proposition to an explicit coefficient universe and adds the exact
specialization proof. No new source theorem is transcribed, and no existing
statement or proof is edited. Manifold assembly and the intrinsic family
criterion are separate targets in `General.RegularAtlasComparison`.
