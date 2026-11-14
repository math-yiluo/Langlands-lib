# Order actions under principal-cover refinement

This derived unit restricts an actual formal order action along a
`BasicAtlas.CoverRefinement` and upgrades its full-family restriction and
gluing equivalence to linearity over that order.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, permits formal groups
obtained by gluing formal groups over localizations. This unit implements
order-compatible refinement within that convention; its constructions are
derived infrastructure, not separately stated theorems of Drinfeld.

The registered source is `drinfeld-1976-coverings-p-adic-symmetric-regions`,
SHA256 `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

The parameters are arbitrary commutative rings `O` and `R` with an
`O`-algebra structure on `R`, a possibly noncommutative ring `D` with an
`O`-algebra structure, and a finite coordinate type in `Type`.
An original varying-law atlas `X`, its actual formal `OrderAction D X`,
and an actual principal-cover refinement `q` are supplied. Covers may be
infinite. Test algebras lie in the universe `v` of `R`; the modules of
complete compatible families lie in universe `v + 1`.

The result concerns actual formal endomorphisms and their full compatible
families. It does not construct an unramified division subfield, special
modules, height descent, framing, presentation classes or a representing
object.

## Formal restriction

`orderChart` maps every original order endomorphism in the chart selected by
`q.source` along the actual localization map `q.chartCoefficient`.
`orderChart_coordinates` identifies the result on every finer-chart test
with extension of that same original endomorphism directly to the test.
The proof uses uniqueness of localization maps, as expressed by
`q.coefficient_comp`, and composition of coefficient maps on series.

`orderChartIso` equips the existing identity-coordinate formal chart
isomorphism and its inverse with the commutation equations for every
element of `D`. `orderTransition` identifies the refined transition
coordinates with the original transition coordinates and then uses the
original formal commutation equation. `orderAction` packages these actual
restricted chart actions and formal transition equations.

## Evaluation and actual descent

`orderChartEquiv` evaluates `orderChartIso` to a `D`-linear chart
equivalence. Its forward and inverse maps preserve each actual tuple.
`orderChartMap` records that identity tuple function as a linear map in
the direction needed for family restriction.

`orderOnPoints` is exactly `q.onPoints` on complete compatible families:
its value at a finer test is the original family's value at
`q.restrictTest` of that test. Its full `D`-linearity follows component by
component from `orderChartMap`.

`orderPointEquiv` uses that linear map as its forward function and the
already constructed `q.fromPoints` as inverse. The latter glues matching
nilpotent coordinate tuples in each original chart. The two inverse laws
are the existing full-family descent equations. Thus the inverse is
actual local coefficient gluing; its linearity follows from the forward
linear map and inverse laws.

`orderOnPoints_natural` uses the original family restriction naturality
equation for every coefficient-algebra map. `orderPointFunctorIso`
packages these equivalences and equations as a natural isomorphism of
`D`-module functors. `orderNilpPointFunctorIso` restricts the same
isomorphism to the full subcategory where the image of the specified
base element is nilpotent.
