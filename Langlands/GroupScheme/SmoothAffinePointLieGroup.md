# The original point group on the chosen smooth affine manifold

For an actual group scheme `G` over `Spec k`, with `k : Type` an `RCLike`
field and `G.X.left` affine, `G.smoothAffineGroupChartedSpace hsmooth`
is an abbreviation for exactly `smoothAffineChartedSpace hsmooth`.
The theorem `G.smoothAffineLieGroup hsmooth` equips the
original group on `RingPoint k G.X k` with a real `C∞` Lie group structure.
Its only smoothness input is the algebraic property
`hsmooth : SmoothOfRelativeDimension d G.X.hom`. Its charted space is
exactly the published `smoothAffineChartedSpace hsmooth`, obtained from
`smoothAffineRegularAtlas hsmooth`. No second atlas is selected and no
analytic comparison premise is required from the caller.

The Lie group theorem applies the published `regularAtlasLieGroup` to that exact
atlas and to the published `regularAtlasComparison.{0,0,0}`. Thus it
reuses the already proved regular-function test for multiplication and
inversion. The local group instance is
`G.ringPointGroup (CommAlgCat.of k k)`, the original categorical group law
on actual relative scheme morphisms. The charted space uses the existing
global regular-function evaluation topology. The published
`smoothAffine_topology_eq_evaluation` applies to the same charts, and
`affinePointsRingPointHomeomorph` identifies the original group-point
evaluation topology with this topology by the identity on actual points.
Its published multiplication, inversion and evaluation equalities record
the original maps explicitly. This module introduces no global group,
topology or chart instance.

`smoothAffine_contMDiff_mul` and `smoothAffine_contMDiff_inv` install these
chosen charts locally, then project the corresponding smoothness fields
from the resulting Lie group structure. Their functions are
literally `(p,q) ↦ p * q` and `p ↦ p⁻¹` for the existing point group law.
`realSmoothAffineLieGroup` and `complexSmoothAffineLieGroup` specialize
the construction to the actual real and complex points, using the exact
published real and complex chart aliases. Their real models are
`Fin d → ℝ` and `Fin d → ℂ`. The published `real_model_finrank` and
`complex_model_finrank` identify their real dimensions as `d` and `2*d`.
There is no positive dimension or point nonemptiness premise, so `d = 0`
and empty point spaces are included.

`smoothAffine_contMDiff_iff_coordinateSmooth.{v,w}` compares families on
these same chosen charts. The source has a real normed model
`E : Type v`, a topological model space `H : Type v`, a model with corners
`I : ModelWithCorners ℝ E H`, and a carrier `M : Type w` with explicitly
assumed topology, `ChartedSpace H M` and `IsManifold I ∞ M`. The repeated
universe `v` matches the published `CoordinateSmooth` interface; the source
carrier has the independent universe `w`.

For `p : M → G.affinePoints (CommAlgCat.of k k)`, the smooth family on the
left is the actual point family
`t ↦ G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p t)`.
The right side is exactly
`G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p`.
The proof composes the published chosen-atlas criterion
`smoothAffine_contMDiff_iff_regularSmooth.{v,v,w}` with the published
`G.regularSmooth_iff_coordinateSmooth`. Both sides test the same actual
global regular-function values in `k`, viewed as a real normed space.
The real and complex theorems
`realSmoothAffine_contMDiff_iff_coordinateSmooth` and
`complexSmoothAffine_contMDiff_iff_coordinateSmooth` give both coefficient
specializations with the corresponding named chart aliases.

This is an internal construction and direct proved-reuse adapter. It
specializes already published atlas, comparison and group transport
results to the named construction in `SmoothAffineManifold`; it adds no
substantial algebraic or analytic proof. The separately published
`smoothAffineGroupManifold` theorem in `AffinePointRegularLieGroupProof`
already proves the existential group-atlas statement. This module records
the stronger choice compatibility needed to use the group operations and
family criterion with the same named charted space as the general affine
construction. Author: Worker 1203.
