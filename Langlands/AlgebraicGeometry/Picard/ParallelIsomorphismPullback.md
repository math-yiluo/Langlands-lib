# The full endpoint pullback of actual Picard arrows

This internal construction identifies the entire parallel-isomorphism
presheaf as an actual endpoint base change. `atlasEndpointPresheaf` retains
both arbitrary maps to the family base on every scheme test.
`atlasArrowEndpoint` records the two maps of an actual arrow and
`familyEndpointMap` records the composites of a test map with two fixed
endpoint maps `a,b`.

`totalParallelIsomorphismPresheaf` retains a map `q` to the common base
and an actual isomorphism between the family pullbacks along `q ≫ a`
and `q ≫ b`. Its natural maps retain the actual arrow and the common
base map. The generic helper `totalParallelArrowMap` verifies naturality
with the coherent isomorphism pullbacks, accounting for associativity
of the two endpoint composites.

`totalParallelIsomorphism_isPullback` proves the full presheaf pullback
universal property. It verifies it on every test using the pointwise
criterion for pullbacks of types: compatibility holds by the component
formulas, the actual arrow and base map uniquely determine a section,
and an arbitrary compatible arrow and base map reconstruct that section.
No test is restricted and no geometric-point or isomorphism-class
replacement is used. This identifies the parallel-arrow presheaf needed
for the actual arrow kernel; quotient construction remains separate.
