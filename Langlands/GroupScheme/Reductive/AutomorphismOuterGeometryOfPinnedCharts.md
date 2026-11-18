# Full outer geometry from pinned constant charts

Worker 592. Internal derived assembly from the supplied-Isom pinned chart
statement, the actual affine pinned atlas of a reductive group scheme,
and exact-orbit quotient geometry. The pinned chart statement is an
explicit hypothesis and no proof of it is supplied here.

For any supplied full automorphism representative of a reductive group,
and any independently supplied full-centre reductive quotient, the first
theorem proves all of the required geometry of any supplied exact outer
quotient: its parameter is separated and étale, its class map is affine,
the positive inner-automorphism map is a closed immersion, and its parameter
is an actual constant scheme after base change to each member of an
étale cover. The cover is the group's affine pinned atlas.

On each chart, the supplied group's pullback is identified with its pinned
model. The pinned statement gives a complete constant family of local
orbit representatives. The existing local-section change-of-base adapter
expresses this family on every original-base test, retaining its projection
to the chart. Exact-orbit local parameter comparison then identifies the
outer parameter's actual pullback with that constant parameter. Fppf
property descent supplies separatedness and étaleness. The comparison uses
a proof of local finite presentation for the actual class map. The theorem
also accepts a proof of its affineness. Both default proofs use the fpqc
property descent for an arbitrary exact outer quotient.
The closed-orbit theorem applied to the identity and composed with group
inversion gives the closed positive inner inclusion.

The second theorem retains the canonical quotient representation `R`
constructed from pinned charts and applies `outerOfQuotientRepresentation`.
The outer quotient has `R.classMap` as its class map.
`QuotientRepresentation.locallyOfFinitePresentation` and
`QuotientRepresentation.classMap_property` give the two class-map proofs on
this same morphism. For affineness the latter uses the affine adjoint group
and descent along surjective flat locally finitely presented morphisms.
Both the full automorphism representative and the pinned chart statement
remain inputs. The geometry holds for all universes, arbitrary bases and
relative tests, and possibly infinite outer label types.

`automorphismOuterQuotientOfPinnedCharts` selects the actual outer quotient
from the proved existence theorem. Its hypotheses remain the supplied
full representative and the explicit pinned classification statement.
