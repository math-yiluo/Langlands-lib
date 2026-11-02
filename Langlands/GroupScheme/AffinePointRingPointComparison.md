# Actual affine group points and the general affine point carrier

Author: Worker 1203.

This is an internal comparison of two published constructions, with no new
algebraic or analytic hypotheses. `G` is an actual group scheme over `Spec R`
and `A` is an `R`-algebra. `G.affinePoints A` and
`PointTopology.RingPoint R G.X A` are both the actual relative scheme morphisms
from `Spec A` to `G`. `affinePointsRingPointMulEquiv` is the identity on those
morphisms and preserves their existing group-object point multiplication.
`ringPointGroup` exposes the existing categorical Hom group through the named
`RingPoint` carrier, which otherwise hides its head symbol from instance search.
This is an explicit definition, used locally here; it installs no global group
instance. The multiplicative equivalence is available without affineness or a
coefficient topology.

When `G.X.left` is affine and `A` has a topology,
`affinePointsRingPointHomeomorph` compares the existing group-point evaluation
topology with the general affine-scheme evaluation topology. It composes the
published `affinePointsAlgebraHomeomorph` with the inverse of
`PointTopology.affineSchemePointHomeomorph`. The underlying maps in both
directions are the identity on relative morphisms, as the two application
lemmas prove. Thus this compares the existing topologies on the actual
carriers and does not declare a new topology instance.

`affinePointsRingPointHomeomorph_evaluation` proves that every global regular
function has the same value under the comparison.
`affinePointsRingPointHomeomorph_mul` and
`affinePointsRingPointHomeomorph_inv` preserve the existing point group law,
and `affinePointsRingPointHomeomorph_postcomp` intertwines the map induced
by any relative morphism of the underlying schemes, whether or not it
preserves the group law.

The provenance is internal: the two existing homeomorphisms use the same
`affineSchemePointEquiv`, and `affineSchemePointEquiv_evaluation` already
identifies that equivalence with group-point evaluation. The proof uses their
inverse identities and the definitional group-object law. This unit constructs
no manifold and proves no smoothness assertion. The algebraic smoothness to
manifold construction and the smooth-family comparison remain separate
obligations in task `ab4a68f8-804a-4381-88f6-4f97d57779a7`.
