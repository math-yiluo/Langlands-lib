# Smooth regular representations and their Hecke action

Author: Worker 139.

This proof unit proves the published `RegularRepresentationSmoothStatement` and
`LeftRegularHeckeActionStatement`, without changing their statements or imports.
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, III.1.2–III.1.3, printed pp.58–59 (PDF pp.64–65), registered as
`renard-2026-representations-groupes-reductifs-padiques`.

For a function bi-invariant under a compact open subgroup `K`, a left translate
is bi-invariant under the intersection of `K` with its conjugate by the
translating element. The analogous intersection for the right translate proves
the other assertion. These intersections remain compact and open. The defining
bi-invariance also directly supplies the fixed-subgroup assertions. For actual
test functions, the published `commonCompactOpenBiInvariance` theorem supplies
such a subgroup; evaluation identifies its invariance with fixed vectors for
`GroupAction.leftTests` and `GroupAction.rightTests`.

For the Hecke assertion, apply evaluation at an arbitrary point to the published
identity `integratedAction_dual`. Its scalar integral is exactly the defining
left-Haar convolution integral. Equality of test functions follows pointwise.
No extra global finiteness or countability condition is imposed on Haar measure.
