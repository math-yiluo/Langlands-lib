# Actions on categorical pullbacks

This internal construction induces a group action on any specified categorical
pullback from compatible actions on its cospan. It works in an arbitrary
category and does not assert analytic continuity.

`pullbackActionEnd` is the unique map whose composites with the two projections
are the corresponding source actions after projection. The commuting cospan
squares and the pullback equation justify the universal-property lift.
`pullbackAction` packages these maps as a monoid homomorphism to endomorphisms:
its unit and multiplication laws follow by composing with both projections and
using pullback uniqueness. `Action.ρAut` then supplies the inverse maps from
inverse group elements, producing a homomorphism to automorphisms.

The two projection lemmas state full categorical equivariance. The construction
uses no compactness, topology, pointwise injectivity, chosen limits, or
quasi-étale stability. Its provenance is the elementary universal property of a
categorical pullback, isolated as an internal helper for Task 7491.
