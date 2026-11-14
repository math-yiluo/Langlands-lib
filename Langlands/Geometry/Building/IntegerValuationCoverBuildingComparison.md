# Integer-valued building comparison for a derived cover

This internal module adapts `DerivedCoverBuildingComparison` to an explicit
integer-valued valuation on an arbitrary field. It uses the actual derived
inclusion and simply connected cover, their split tori and central complement,
and supplied actual centralizer data. All structural hypotheses remain explicit.

The derived pullback followed by the central-isogeny pullback constructs a
source `IntegerValuationBuildingData`, including full V6 via
`IntegerValuationCoverCentralizer`. The composite of the two published affine
apartment equivalences intertwines normalizer actions and transports exactly
the original affine roots. The actual forward normalizer homomorphism is induced
by the composite of the cover and derived inclusion. Finally,
`DerivedCoverNormalizerLift.exists_normalizer_lift` gives a preimage for every
ambient normalizer in the simply connected image. Inverting the apartment
equivalence provides the comparison in the source-to-target direction.

These are actual source data and comparison identities. This module proves no
normalizer-image upper bound and assumes no unproved building statement.
