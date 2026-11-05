# Smooth scheme maps are open on complete-field points

Author: Worker 208.

`completeFieldSmoothPointOpen.{u}` proves exactly the published
`CompleteFieldSmoothPointOpenStatement.{u}`. For a complete nontrivially normed
field `K`, a smooth relative morphism between schemes locally of finite type
over `Spec K` induces an open map on actual `RingPoint K X K` spaces with the
published affine-chart topologies. All the target hypotheses are retained; no
affineness, separatedness, quasi-compactness, surjectivity, characteristic or
local-compactness assumption is added.

## Implemented proof

`isOpenMap_affineSmoothPointMap` handles arbitrary affine schemes over `K`.
It installs the actual global-section pullback
`affineCoordinatePullback K f` as the algebra structure on the source coordinate
ring over the target coordinate ring. Compatibility with the given `K` maps
gives the scalar tower. Mathlib's
`HasRingHomProperty.iff_of_isAffine` identifies smoothness of the scheme map
with smoothness of this ring homomorphism. The already proved
`smoothAlgebraPointOpen` therefore makes restriction of actual algebra points
open. Naturality of `affineSchemePointEquiv` identifies this restriction with
actual postcomposition of scheme points, and the two published affine point
homeomorphisms transport openness.

`isOpenMap_smoothSchemePointMap` glues this affine result. Given a point of an
open source set, choose an affine target open around its image and an affine
source open contained in its inverse image. The actual restricted morphism
`Scheme.Hom.resLE` remains smooth and respects the base. The original point
lifts to the source chart, since a field is local and membership of the closed
point implies containment of the whole point morphism in that open. Pull the
source set back along the continuous chart map, apply affine smooth openness,
and map the resulting open image into the target through its open affine-chart
embedding. The resulting target open contains the chosen image point and lies
inside the original image, by the factorization of the restricted morphism.
This proves openness for the published final topology.

The two helpers do not need local finite type of the structure morphisms:
that is a derived strengthening obtained from the arbitrary-coordinate-algebra
smooth proof and the existing chart results. The final theorem applies this
helper with every hypothesis of the published source-qualified target.

## Source and scope

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`:
printed p.11, discussion after Proposition 4.4 and before Theorem 4.5, and
printed p.12, proof of Theorem 4.5, step (i). The latter passage states precisely
the locally finite-type assertion proved by the final theorem. The proof
follows its affine local reduction, using the published algebra-map proof for
the analytic step and the actual scheme-point chart constructions for gluing.

This proof supplies the local complete-field assertion. The additional
almost-all integral-point surjectivity and the adelic smooth-openness theorem
remain separate obligations of the parent task.
