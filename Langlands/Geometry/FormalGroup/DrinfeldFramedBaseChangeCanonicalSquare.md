# Chart-independent fixed-frame comparison in the actual base-change square

This module identifies the fixed-frame test comparison used by the
actual extended framing with the direct coefficient-map comparison having no
target-chart parameter. It derives from complete formal coordinate equations
and actual inverse laws; it makes no new literature assertion.

The generic lemmas prove identity series for actual global-cover equality
transport, restriction of scalar composition, scalar-retyped global
normalization and source coefficient-chart comparisons. Actual atlas-map
composition retains these series. The source quotient-frame comparison is its
implemented composite of those existing actual maps. Its inverse chart map has
identity series by its actual inverse equation.

`baseChangeFrameChartIso_hom_coordinates` applies these constituent equations
to the exact four formal maps used by `baseChangeFrameChartIso`.
`baseChangeFrameChartIso_eq_global` compares it with
`baseChangeGlobalFrameTestIso` by complete formal-map extensionality: both have
identity coordinate series, and the actual forward map determines the inverse.
This proves equality of actual formal isomorphisms rather than equality of
point evaluations.

`chartFraming_baseChange_canonical` applies rationalization and postcomposition
to that exact equality by congruence, then composes it with the previously
proved whole normalized framing equation. The fixed-frame side now
uses the direct coefficient-map comparison and is independent of the target
chart. `baseChangeCanonicalFramingSquare` packages those four actual full-order
rational maps and their proved equation in the existing commuting-square
structure. No additional framing or original chart is chosen.

The parameters retain the local field, finite-dimensional central division
algebra, embedded field, coefficient and residue fields, fixed height-certified
frame and Nilp objects in universes `{v,u}`. Covers may be infinite and scalar
maps may merge generators. Generic identity-coordinate composition uses one
finite coordinate type, as do these special atlases. Preservation of the
original framed comparison square and descent to class functoriality are
outside this module; they are `framingSquare_baseChange` in
`DrinfeldFramedComparisonBaseChange` and the functor of
`DrinfeldFramedClassFunctor`.
