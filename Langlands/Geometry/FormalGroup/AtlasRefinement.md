# Actual principal-cover refinement of formal module atlases

`BasicAtlas.CoverRefinement.atlas` restricts the possibly varying chart laws of
an actual formal O-module atlas to a finer principal cover. The constructed
map `CoverRefinement.onPoints` restricts full compatible families of nilpotent
tuples, is O-linear, and is natural in the coefficient algebra.

## Provenance and scope

This is derived infrastructure for Drinfeld's convention that formal groups
may be glued from laws over localizations: Drinfeld, *Coverings of p-adic
symmetric regions* (1976), printed p.109, paragraph immediately before section
2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
This construction is not a separate theorem stated in that paragraph.

O and R are arbitrary commutative rings with an O-algebra structure on R.
The coordinate type is finite and belongs to `Type`; coefficient test
algebras belong to R's universe v. Both covers can be infinite and their
generators span the unit ideal. No global chart law is assumed.

`CoverRefinement X` supplies a finer cover, a chosen original chart for each
new chart, and proof that the original generator is a unit in the new
localization R[1/b]. This is actual containment of principal opens, rather
than a comparison of abstract point carriers. The new chart law is
constructed by coefficient extension of that original chart. Arbitrary
changes of coordinates between distinct presentations are not inputs here.

This unit constructs the atlas and the restriction transformation. It does
not yet prove that restriction is invertible, construct a quotient of atlas
presentations, or define framing, heights, moduli or representability.

## Restricted laws and transitions

`source_unit` maps the localization containment into any test where the finer
generator is invertible. `chartCoefficient` is the actual localization lift
from the original chart ring to the finer chart ring.
`chartCoefficient_algebraMap` records its value on R, and
`coefficient_comp` proves that its composite into a test equals the direct
original localization lift, by uniqueness of maps from a localization.

`chart` extends the original formal module law along this coefficient map.
`chartIso` uses the proved coefficient triangle to construct an isomorphism
between this restricted law over a test and the original law over that test.
It has identity coordinate series; the equality of addition and scalar
series is proved rather than supplied as an assumption.

`transition` conjugates the original transition by these chart
identifications. `transition_coordinates` proves that its coordinate series
are exactly the original transition series. The atlas self-transition,
cocycle and coefficient naturality equations then follow from the original
atlas equations. `atlas` packages the result with the supplied finer cover.

## Actual points and restriction

`chartEquiv` evaluates the actual chart isomorphism on nilpotent tuples.
Both directions preserve the raw tuple, as proved by its two application
lemmas. `chartMap` exposes that identity tuple function with its established
O-linearity for the two formal laws.

`transitionPoints` proves that evaluating a refined transition is the same
as evaluating the original transition between its chosen source charts.
`restrictTest` sends a test of the finer atlas to its actual source chart,
using the proved containment to produce the unit condition.

`onPoints` evaluates an original compatible family at each of these tests.
The original coefficient compatibility proves coefficient compatibility of
the restriction, and `transitionPoints` and the original chart
compatibility prove its transition equation. `chartMap` proves O-linearity
for the actual formal addition and O-action, rather than coordinatewise
addition. `onPoints_apply` gives the restriction formula at every test.

`onPoints_natural` follows directly from precomposition of tests.
`pointNatTrans` packages the same actual restriction maps as a natural
transformation between the two module-valued point functors.
