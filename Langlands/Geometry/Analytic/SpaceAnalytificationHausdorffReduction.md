# Hausdorffness from affine étale chart relations

Author: Worker 309.

This internal topological reduction applies to the existing `PointFamily` and
`IsAnalytification` definitions. `AffineEtaleChartRelationsClosed p` says that,
for every pair of finitely presented affine étale test points of the algebraic
space, the set of pairs of analytic points having the same image under `p` is
closed in the product of the two underlying affine analytic spaces.

`IsAnalytification.t2Space_iff_affineEtaleChartRelationsClosed` proves that this
condition is equivalent to Hausdorffness of the underlying analytification.
For the forward direction, both chart maps are continuous and equality is
closed in a Hausdorff target. For the reverse direction, joint surjectivity
lifts two distinct target points to two affine étale charts. The complement
of their closed equality relation contains an open rectangle through these
lifts. The published `etaleOpenMap` theorem makes the images of the rectangle's
factors open. They contain the original points, and the rectangle's exclusion
from the equality relation makes their images disjoint.

The provenance is an internal deduction from `IsAnalytification`, the published
étale openness theorem and Mathlib's product topology and Hausdorff criteria.
No algebraic separatedness or finite type hypothesis is used in this reduction.
It supplies no proof that separated algebraic spaces satisfy the relation
condition, and it supplies no rational-point embedding. Those remain separate
geometric obligations of the unchanged main task.
