# Uniqueness of admissible varying-dimension analytic structures

This proof follows the uniqueness argument of Brian Conrad, *Weil and
Grothendieck approaches to adelic points*, December 31, 2011, printed pp.15–16
(Proposition 5.4). The original source is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The statement being proved is the Library's conditional uniqueness formulation:
for any nontrivially normed field, two supplied admissible families are
equivalent. This formulation does not assume completeness and does not construct
either family; Conrad's existence assertion assumes completeness.

On affine space the normalizing coordinate equivalences of the two families
agree with the same actual polynomial coordinates. Composing the first with the
inverse of the second therefore gives the identity, analytic in all charts.

For an étale morphism to a space on which the families agree, functoriality for
the first family and an inverse branch for the second pull back agreement.
Conversely, an inverse branch for the first family and functoriality for the
second transfer agreement from an étale source to its image. All compositions
use the pointwise calculus in `DimensionPointAtlasCalculus`; local inverse laws
identify the composites with the actual identity near the chosen point.

At a point `x` of an arbitrary smooth, quasi-separated, locally separated
algebraic space, the proof factors the actual section through its dimension
piece. That piece is smooth of pure dimension `n`, so
`smoothPureDimensionalAffineChart` gives an affine étale scheme chart with a
rational point over `x`. A standard-smooth basic open around that point has an
étale map to affine `n`-space. Agreement therefore holds on this open, and the
étale composite from the open through the dimension piece to the original space
transfers agreement to `x`. Pointwise analyticity gives analyticity in every pair
of charts on the original space. Reversing the two families proves equivalence.

The exact theorem `smoothSourceDimensionAnalyticUniqueness.{u}` has type
`SmoothSourceDimensionAnalyticUniquenessStatement.{u}`. The argument works in
every universe and assumes neither a finite dimension range nor that either
family comes from a pure-dimensional `AnalyticPointStructure`. The supplied
admissibility hypotheses provide functoriality, analytic étale inverse branches,
and affine normalization; the separate analytic-transition conjunct is not
needed by this uniqueness proof.
