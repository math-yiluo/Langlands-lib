# Actual comparison isomorphisms between specified original test charts

This internal unit constructs `Comparison.testIso`: the actual integral
full-order formal isomorphism from a specified original source chart to a
specified original target chart on a test algebra. A supplied invertible finer
comparison chart specifies its middle formal map. The construction follows the
source transition, inverse left refinement chart identification, given actual
comparison chart isomorphism, right refinement identification and target
transition. All maps and both actual inverses are retained.

`testIso_hom_coordinates` computes the complete forward series, using the
complete identity series of refinement chart identifications. The formula
contains the actual comparison series and the two original transitions.
`testIso_independent` applies the previously proved complete coordinate
transport equation to two supplied finer charts. Full formal-map extensionality
and inverse uniqueness then identify the whole integral isomorphisms on the
fixed original charts. Equality of point evaluations is not used.

The coefficient and acting rings have separate universes and arbitrary finite
source and target coordinate types. All specified finer and original chart
generators have their actual unit evidence in the test ring. Covers may be
infinite. This unit does not yet assert coefficient-extension compatibility or
framed comparison base change.
