# Fixed-frame test comparisons defined directly by coefficient maps

This module constructs the fixed-frame comparison on a new Nilp-base
test algebra directly from the actual coefficient maps, without a target chart
parameter. It derives from the actual scalar-composition and equality-transport
constructions; it makes no new literature assertion.

`OrderAction.mapReAlgebraIso` compares two actual coefficient extensions whose
scalar structures are equal and whose underlying ring maps agree. Equality
elimination followed by algebra-map extensionality gives the actual identity
formal isomorphism. Both directions have complete identity coordinate series.
The scalar-composition coordinate equations and scalar-transport coordinate
equations record the corresponding actual forward and inverse formal maps.

`baseChangeGlobalFrameTestIso` first uses the actual scalar-composition
isomorphism from the new globally extended fixed frame on the test algebra to
the frame extended by the composite coefficient map. The two composite maps
from the residue field to the same test ring agree. The inverse of
`mapReAlgebraIso` then changes to the scalar-transported original composite map,
and the inverse scalar-transported old composition isomorphism reaches the
scalar-transported original global frame on that test algebra. It retains both
actual formal inverse maps and commutes with the entire acting order.

The two coordinate equations prove that both complete formal maps have
identity series. Their proofs use the proved constituent coordinate equations
and identity-coordinate composition. There is no chart choice and no inference
of formal-map equality from point evaluation. Equality with the chart-dependent
comparison in `DrinfeldFramedBaseChangeCharts` is proved separately, as
`baseChangeFrameChartIso_eq_global` in `DrinfeldFramedBaseChangeCanonicalSquare`.

The parameters retain the local field, finite-dimensional central division
algebra, embedded field, coefficient and residue fields, fixed height-certified
frame and Nilp objects in universes `{v,u}`. No target cover or target test chart
is an argument of this comparison. The generic scalar-comparison helpers use
finite coordinate types and coefficient rings in one universe. Framed comparison
compatibility, class functoriality, actions and representability are outside
this module; the first two are in `DrinfeldFramedComparisonBaseChange` and
`DrinfeldFramedClassFunctor`, and actions and representability remain separate.
