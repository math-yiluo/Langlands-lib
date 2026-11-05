# Actual projective arithmetic models and generic fibers

This module constructs concrete projective arithmetic models for the full-product
comparison of Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.10, Example 4.3. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source considers positive-dimensional projective space. The constructions
also include dimension zero as derived infrastructure; no density or
non-discreteness conclusion is asserted here.

`projectivePointScheme R n` is the existing polynomial-Proj projective scheme,
with its published actual structure morphism, viewed in Over(Spec R). Its
properness is the existing `projectiveSpaceToSpec_isProper` theorem. The module
introduces no alternative projective-space carrier.

`projectivePointSchemeBaseChangeIso R A n` identifies its actual pullback along
Spec A to Spec R with the same projective construction over A. It uses the
published `AlgebraicGeometry.ProjSpace.isPullback_map` theorem from the Anthropic
FLT port, imported by Lean name. The existing projective structure maps agree
with the port's structure maps. The pullback comparison and its second-projection
identity give an isomorphism over Spec A. This is an internal reuse adapter; it
asserts no new geometric base-change theorem beyond that published result.

For every finite set S of curve places, `curvePlaceProjectiveModel` is projective
space over the actual outside-S integer ring. Its
`curvePlaceProjectiveGenericFiberIso` is the preceding actual base-change
isomorphism for the literal subring inclusion into the original field F. The
`curvePlaceProjectiveAdelePointTopology` is exactly the arithmetic spread topology
from this model and isomorphism. The analogous three number-field constructions
use the original outside-S integer ring and the full arithmetic levels, including
every infinite factor.

All constructions have an arbitrary common universe. The relative scheme and
base-change adapter allow arbitrary commutative rings. The curve topology uses
the existing perfect-constant, specified-rational-function-action function-field
inputs; its algebraic model and generic-fiber isomorphism do not need those extra
inputs. Every finite initial set, including the empty set, is allowed. The module
constructs the model data without assuming an unspecified spread or generic-fiber
isomorphism. The actual adelic full-product comparison, its compactness and
Hausdorffness, rational-point density, and affine-line subspace topology remain
separate obligations.
