# Local Zariski density of actual rational points

Author: Worker 135.

`Langlands.AlgebraicGeometry.PointTopology.RationalLocalDensityStatement.{u}`
is a proposition about an arbitrary nonarchimedean local field `F` and
an affine integral scheme `X` smooth over `Spec F`. It uses the actual
identity-test morphisms `RationalPoint F X` with the published
`rationalPointTopology F X`. The target of evaluation is the underlying
scheme space of `X`, with its Zariski topology.

The proposition requires two conclusions. Evaluation of each actual
rational-point morphism at the unique point `IsLocalRing.closedPoint F`
of `Spec F` is continuous. The image of every nonempty open subset of the
rational-point space under this evaluation is Zariski dense in `X`.
The openness premise refers to the local-field evaluation topology on
rational points, not the Zariski topology on `X`. No rational point is
assumed to exist unless the supplied open subset is nonempty.

This is an internal prerequisite for Haar conullness of actual dynamic
open cells. It strengthens the global density interface in
`GroupScheme.Rational.LocalFieldDensity` by retaining each prescribed
analytic open subset. The intended proof transfers the
neighbourhood-controlled algebra-point separation statement
`RingTheory.LocalFieldDensity.LocalSeparationStatement` through the
canonical affine-coordinate and rational-point comparisons. The
continuity part follows from evaluation of regular functions and the
basic-open basis of the prime spectrum. No external literature assertion
is claimed for this extracted interface.

This file defines a statement only. Its proof, the integral and
Noetherian adapters for connected smooth affine groups, the Haar-null
closed-set result, and the actual dynamic open-cell complement
comparison remain separate obligations.
