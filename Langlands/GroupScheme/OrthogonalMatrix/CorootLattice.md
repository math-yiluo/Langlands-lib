# The integral coroot lattice of the split even orthogonal group

This internal adapter identifies the integral coroot span of any supplied root
datum of `OrthogonalMatrix.identityTorus l k` with the integer lattice generated
by distinct coordinate pair sums and differences. The field `k` is arbitrary,
and the finite index type `l : Type` has at least three elements.

The published type D coroot calculation identifies the coroot of `w(x) + w(y)`
with `w(x)^∨ + w(y)^∨`. Its coordinate sum is even for each of the four choices
of signs. Conversely, the roots with indices `(inl a, inl b)` and
`(inl a, inr b)` give respectively every pair sum and difference, for `a ≠ b`.
Taking integer spans proves `map_corootSpan_eq_pairLattice` under the published
coordinate equivalence for the split torus.

`corootQuotientEquiv` transports the quotient through this coordinate equivalence
and applies `TypeDParityLattice.quotientEquiv`. Thus `card_corootQuotient` gives
cardinality two for the actual cocharacter lattice modulo its coroot span.

The provenance is this direct comparison of two existing constructions, using
the published `OrthogonalMatrix.TypeD` root and coroot formulas and the explicit
integer calculation in `Langlands.LinearAlgebra.TypeDParityLattice`. No spin
cover, comparison with a quaternionic form, or kernel identification is assumed
or concluded here.
