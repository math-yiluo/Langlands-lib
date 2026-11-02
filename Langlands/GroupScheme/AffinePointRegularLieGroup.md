# Actual group operations and the smooth-affine-group target

Author: Worker 1203. The generic regular-atlas and comparison interfaces were
authored by Worker 274.

For an actual affine group scheme `G` over an `RCLike` field `k`, let `A` be a
`RegularAtlas k G.X d`. `regularAtlasLieGroup` constructs a real `C∞`
`LieGroup` property on the actual `RingPoint k G.X k` carrier, equipped with
`A.chartedSpace` and the published evaluation topology. The group is the
original categorical point group, exposed locally by `ringPointGroup`.
There is no new group law, topology, or global instance.

The construction explicitly assumes
`regularAtlasComparisonStatement.{0,0,0} k G.X d`. This assumption supplies
both the manifold structure of every regular atlas and the intrinsic
regular-function family criterion for sources in `Type`. Smoothness of the
two product projections gives regular-smooth projection families; preservation
under actual point multiplication gives the regular-smooth product map; the
criterion then proves that map is smooth. For inversion the same argument
starts with the identity family and uses `regularSmooth_inv`.

`regularAtlas_contMDiff_iff_coordinateSmooth` applies the generic family
comparison to a parameter family transported by the identity homeomorphism
from `G.affinePoints k` to `RingPoint k G.X k`. It then uses the proved
equality with `G.CoordinateSmooth` for the identity coefficient map. Its
source real model with corners, charted space, and `IsManifold I ∞ M`
hypothesis are explicit.

This is internal derived transport of the existing group-operation
preservation results through the analytic family criterion. It does not
prove that comparison assumption or construct an atlas from algebraic
smoothness. Those remain separate obligations. In particular, this conditional
construction is not the full smooth-affine-group existence theorem.

`smoothAffineGroupManifoldStatement.{v,w}` is the exact Prop-valued existence
target. Its input is the algebraic condition
`SmoothOfRelativeDimension d G.X.hom`, with `IsAffine G.X.left` explicit in
the declaration. Its output is one `RegularAtlas k G.X d` for which both the
original actual point group is a real smooth `LieGroup` and the transported
family criterion agrees with `G.CoordinateSmooth` for `RingHom.id k`.
The source real normed model `E' : Type v`, topological model `H' : Type v`,
model with corners `I'`, charted space `M' : Type w`, and
`IsManifold I' ∞ M'` assumption are explicit. The equal universes of `E'`
and `H'` follow the existing `CoordinateSmooth` interface.

`realSmoothAffineGroupManifoldStatement` and
`complexSmoothAffineGroupManifoldStatement` specialize this target to actual
real and complex group schemes. Their real models are `Fin d → ℝ` and
`Fin d → ℂ`, respectively; `real_model_finrank` and
`complex_model_finrank` in `RegularCharts` identify their real dimensions as
`d` and `2 * d`. There is no positivity assumption on `d`.

The target keeps the actual relative-morphism carrier, original group laws,
and existing evaluation topology throughout. It assumes no analytic chart or
manifold as input. Its expected proof combines the separately stated
algebraic chart-existence and analytic comparison theorems with the
conditional transfer above. This file states that full target without
proving it, so publication of this interface alone establishes no implication
from algebraic smoothness to a manifold.
