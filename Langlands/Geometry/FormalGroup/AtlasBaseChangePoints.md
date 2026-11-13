# Compatible-family points under coefficient extension of formal atlases

For a supplied actual formal O-module atlas X over R and any R-algebra S,
this module constructs an O-linear equivalence between the original atlas
points on each restricted S-test and the full compatible-family points of
`X.baseChange S`. It proves naturality and the corresponding natural
isomorphism, including its restriction to nilpotent coefficient tests.

## Source, provenance and hypotheses

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), in the paragraph immediately before section 2, permits formal
groups glued over localizations of the base. Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The full-family comparison here is an internal consequence of the actual
atlas equations and the localization coefficient construction. It is not a
separately numbered assertion of Drinfeld's article.

O and R are arbitrary commutative rings with an O-algebra structure on R.
The fixed coordinate type sigma is finite and belongs to `Type`.
`S : CommAlgCat.{v} R` and all test coefficient algebras have universe v.
The supplied principal-open cover may be infinite. Its image cover and
chosen original preimages are exactly those constructed by
`AtlasBaseChange`. Neither flatness nor injectivity of R to S is assumed.

`Point` means the actual simultaneous solution module of all coefficient
naturality and formal chart-transition equations from `BasicAtlas`.
A family assigns nilpotent coordinate tuples after every chart test map;
it is not a chosen tuple or an assumed glued formal scheme. The family
module and the target `ModuleCat` have universe v+1. Structural O-actions
use the existing local `coefficientAlgebra` and `coefficientScalarTower`
instances.

## Forward restriction

`restrictChartTest` restricts an S-test algebra and its test map to R and
selects the original preimage of its image generator. `baseSource_unit`
provides its actual invertibility condition. `baseChangeTransitionPoints`
identifies evaluation of the new transition with evaluation of the
original transition on the restricted test; this follows from the proved
equality of their coordinate series.

`baseChangeChartMap` is the identity on the underlying nilpotent tuples,
with the O-linearity of the actual identity-coordinate chart isomorphism.
It copies that linear map with a definitionally identity function using
the proved application formula. This identifies the actual addition and
scalar operations even though the displayed chart laws differ.

`toBaseChangePoints` sends an original compatible family x to the family
whose value at t is `x.val (restrictChartTest t)`. Original coefficient
naturality proves the first new compatibility equation, and the original
transition equation together with `baseChangeTransitionPoints` proves the
second. The copied chart map proves addition and scalar compatibility.
`toBaseChangePoints_apply` records the actual component formula.

## Constructed inverse

For an original test map phi from the restricted source A to B,
`liftTestAlgebra` equips B with its S-action through S to A to B.
`liftTestMap` is the resulting S-linear map from A. `unliftTestMap` is the
identity ring map from the restricted lifted test to the original B;
`liftTest_R` proves that the actual R-actions agree. `liftTestHom` uses the
original coefficient homomorphism to compare two such induced S-tests.

`imageChart` sends an original generator to its actual image in S.
`liftImage_unit` and `liftSource_unit` give the invertibility conditions in
the induced test and in the original B. `liftChartTest` and `liftValue`
then evaluate a new family on the induced S-test and that image chart.
The value is viewed in the original chosen-preimage chart of B.

`liftValue_natural` follows from the new family's coefficient naturality.
`liftTest_transition` uses the original transition naturality along
`unliftTestMap`: its underlying ring map is the identity, so its mapped
coordinate series are unchanged. Combining this with the new transition
equation gives `liftValue_transition` over the original B.

`fromBaseChangeFamily` applies the original transition from the chosen
preimage of the image generator to the requested original generator.
Thus it recovers a component even when the chosen preimage is a different
original chart. `fromBaseChangeFamily_compatible` proves coefficient
naturality by transition naturality and `liftValue_natural`. The two
transition cocycle equations and `liftValue_transition` prove chart
compatibility. `fromBaseChangePoints` packages this actual family.

## Inverse equations and functors

`toBaseChangePoints_liftValue` uses original coefficient naturality along
`unliftTestMap` to identify restriction followed by a lifted-test
component with the original component. Its ring map is the identity.
The original chart compatibility equation then proves
`from_toBaseChangePoints` at every test.

For the other direction, `liftRestrictionHom` is the identity ring map
from the lift of an already supplied S-test to that S-test. Its S-linearity
is the supplied test map's scalar compatibility. `imageChart_unit` gives
the test's actual unit image condition. New-family coefficient naturality
along this map proves `liftValue_restrict`.

`imageChart_baseSource` identifies the image of the chosen original
preimage with the given image generator. `baseFamily_chart_congr` handles
equality of chart indices, and `transitionPoints_of_eq` evaluates an
original transition between equal chart indices as the identity. These
facts prove `to_fromBaseChangePoints_component`, then
`to_fromBaseChangePoints` by family extensionality.

`baseChangePointEquiv` uses `toBaseChangePoints` as its linear forward map,
`fromBaseChangePoints` as its inverse, and the two proved inverse
equations. The `apply` and `symm_apply` lemmas expose these constructions.
`toBaseChangePoints_natural` checks components after precomposing a test
map. `baseChangePointFunctorIso` packages the resulting natural
isomorphism from `restrictCoefficientFunctor` along the structural
O-algebra map R to S, followed by `X.pointFunctor`, to the point functor
of the extended atlas. It reuses the existing coefficient restriction
functor.

For any pi in R, `baseChangeNilpPointFunctorIso` restricts that same
isomorphism along `Nilp.forget S (algebraMap R S pi)`. Its source is the
original point functor on restricted S-tests; its target is the extended
atlas's actual nilpotent-test point functor. No nilpotence hypothesis on
R or S is needed for the unrestricted comparison.

This unit proves the full comparison for the constructed image-cover
atlas. It does not prove independence of chosen preimages, iterated
base-change coherence, refinement descent or presentation independence.
It does not construct a division-order action, specialness, height,
framing module, moduli object or representing formal scheme.
