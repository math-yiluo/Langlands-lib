# Analytic properties of universe lifts

This companion is internal infrastructure derived from the published
equivalence-invariance laws. It adds no original literature theorem or
classification assertion.

`Langlands.isUnitarizable_universeLift_iff` specializes
`isUnitarizable_iff_of_equiv` to the actual `universeLiftEquiv`. It applies to
any group and any complex module, with no topology on the carrier.

For an actual `PadicField.{uF} p`, its supplied `TopologicalData`, and finite
rank `n : ℕ`, the methods `isTempered_universeLift_iff` and
`isSquareIntegrable_universeLift_iff` similarly specialize the existing
`isTempered_iff_of_equiv` and `isSquareIntegrable_iff_of_equiv`.
They preserve the published analytic predicates, including quantification over
Borel Haar measures on the actual central quotient. The field universe `uF`,
source-carrier universe `uV`, and lift universe `uX` are independent.

The final checked example starts with
`A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)` and explicitly
chooses `SmoothRep.universeLift.{uF} A` in
`SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)`.
It packages the actual representation equivalence and both directions of
irreducibility, admissibility, unitarizability, temperedness, and
square-integrability. This is the universe specialization required to pass a
lifted representative to the existing classification interfaces and transport
these properties back afterwards.

There is no smallness, resizing, finite-dimensionality, or classification
assumption. The example neither applies an unproved classification target nor
claims an isomorphism in two different fixed-universe categories. Whittaker
functional transport is outside this module.
