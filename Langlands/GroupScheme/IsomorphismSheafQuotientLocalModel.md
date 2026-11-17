# Local outer quotient models before a global Isom scheme is supplied

Worker 812, reusing Worker 182's action transport identities. This internal
adapter uses the actual base-change comparisons, full local-chart
representation, and supplied outer quotient. No new literature theorem or
global Isom scheme is assumed.

Given a base morphism `b : U → S`, a full Isom representative `I` for the
pullbacks of `G,H`, and an outer quotient `O` for the pullback of the supplied
source action `a`, the constructor `I.localQuotientPresentation b a O` gives
an `ActionQuotient.LocalPresentation a (Over.mk b)` over the original base.
It assumes the local quotient map is locally finitely presented, and the
quotient parameter is étale and separated over `U`. The remaining flatness
and surjectivity come from `O`.
`localQuotientPresentationOfSmooth` derives the finite-presentation condition
when `I`'s parameter is smooth over `U`: its structure map is the composite of
the class map with the étale quotient structure map, and the published
finite-presentation cancellation lemma applies to that composite.

The Isom parameter viewed over `S` represents the full original Isom
presheaf times `U`, by `localChartIso`; its parameter projection is retained.
The local quotient parameter and class map are likewise viewed over `S`.
Their geometric properties concern the same underlying scheme morphisms.

The kernel comparison is checked on every old-base scheme test. Equality of
parameter projections gives a common `U` structure to the test. The published
`ChangeOfBase.test` and `testIso` make that structure and its old-base
identification explicit. Restricting the chart families to this identification
and applying the family base-change equivalence recovers `I`'s universal
families. Worker 182's `baseChangeFamily_twist` identifies their source actions.
The unique local orbit point supplied by `O` is transported to the original
test by the group-point equivalence, and refinement by the inverse test
isomorphism recovers the original family equation. Conversely, an original
orbit point gives a local one, and `O.invariant` gives equality of classes.

The result is local quotient data for the canonical sheaf quotient, before a
global Isom scheme exists. It still requires the local representatives and
outer quotients with the stated geometric properties.
