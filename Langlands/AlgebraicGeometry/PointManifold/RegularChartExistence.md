# Algebraic smoothness to regular local charts: exact target

`regularChartExistenceStatement k X d` states that the algebraic hypothesis
`AlgebraicGeometry.SmoothOfRelativeDimension d X.hom` supplies a
`RegularAtlas k X d` on the actual relative point space `RingPoint k X k`.
The scheme is affine and the coefficient field is `RCLike` in `Type`.
`realRegularChartExistenceStatement` and
`complexRegularChartExistenceStatement` are the actual real and complex
specializations.

This is a proposition definition, not a theorem or an assumed instance.
Its conclusion is the existence of charts, with no chart, rank, or manifold
input in its hypothesis. Mathlib's algebraic smoothness condition is given
by local standard-smooth presentations of constant relative dimension.
The target includes `d = 0` and an empty actual point space.

The output chart model is `Fin d → k`, used as a real normed space.
The existing `RegularCharts` dimension formulas give real dimension `d`
over the reals and `2*d` over the complexes. Every chart is a partial
homeomorphism for the published regular-evaluation topology. Its forward
coordinates are quotients of global regular functions with denominators
nonzero on its source, and every global regular function pulls back
smoothly on its inverse target. These are obligations in the conclusion.
The analytic atlas-assembly and smooth-family criterion are separate
targets in `RegularAtlasComparison`.

The statement is a derived affine, real-smooth specialization of the
scheme case underlying Brian Conrad, *Weil and Grothendieck approaches
to adelic points*, December 31, 2011, Proposition 5.4, printed pp. 15–16
(registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).
The local inverse-function construction motivates this target; Conrad's
proposition does not state this exact rational-coordinate interface or
the global-regular-function family criterion.

A proof must construct the local charts from algebraic standard-smooth
or étale presentations and a justified analytic inverse or implicit
function theorem, including the required inverse evaluation formulas.
The proposition remains unproved until its separate proof task is
accepted and published.
