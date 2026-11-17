# Continuous action lifts on finite domain-chart wide pullbacks

Work over a complete ultrametric normed field with equal space and chart
universes. `ActionLift.toAction` bundles the actual action of the lift's open
subgroup as a categorical action. Its automorphism-valued action equals the
original action.

`ActionLift.invariantDomain` constructs an action lift on the composite of an
invariant analytic-domain inclusion with the original map. It keeps the same
open subgroup. Its action is the actual analytic restriction, and continuity
follows from `IsContinuousAction.invariantDomainAction`. The domain inclusion
commutes with these actions as an equality of complete analytic morphisms.

Let `C` be a `FiniteCompactDomainChartCover U`, let `l` be an action lift on
`U → X`, and supply an action `σ i` of `l.subgroup` on every selected chart source
such that each chart arrow commutes with these actions. The stored isomorphism
from the source to its ambient domain shows that every point of that domain
comes from a source point. Equivariance and the image property of the chart
arrow therefore prove invariance of the domain. This argument does not require
continuity of the supplied source actions.

For any finite nonempty tuple of chart indices, membership in `wideDomain` is
membership in every selected domain, so the intersection is invariant.
`wideActionLift` restricts `l` to this actual intersection and gives a continuous
action lift on the already constructed `wideObj`. Its base and every projection
are equivariant under the original common subgroup. Projection equivariance
uses the wide-pullback triangle and monicity of the selected chart arrow, hence
establishes an equation of full analytic morphisms.

This is internal infrastructure derived from the published domain-chart wide
pullback, invariant-domain action and continuity constructions. It supplies
actions on those actual limiting cones in every finite nonempty tuple degree.
Together with the existing compactness theorem, the same cones are compact
Hausdorff when `U` is Hausdorff. The construction concerns actual domain-chart
arrows and does not assert existence of compatible actions on arbitrary covers,
general quasi-étale fibre products, or the global comparison theorem.
