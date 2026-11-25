# Universe reduction for the cyclic idele-class Herbrand quotient

`CyclicIdeleClassHerbrandQuotientUniverseReduction.{u, v}` states the
implication from `CyclicIdeleClassHerbrandQuotient.{v, v}` to
`CyclicIdeleClassHerbrandQuotient.{u, v}`. The first assertion ranges over
number fields `F` and `E` both in `Type v`; the second allows `F : Type u`
and `E : Type v`, with the universes independent.

Both assertions are the existing Library proposition. They use the actual
`relativeIdeleClassCohomology`, require finiteness in degrees one and two,
and state that the degree-two cardinality is the extension degree times
the degree-one cardinality for every cyclic Galois extension. Degree-one
extensions are included. This module does not redefine that proposition,
change its coefficient action, or assert an unconditional Herbrand formula.
It states the implication without proving it.

This is internal derived content about the formalization's universes,
not a separately attributed arithmetic theorem. The intended reduction
replaces `F` by the bottom intermediate field inside `E`. Its carrier lies
in `Type v`, its extension degree is unchanged, and the actual `E`
idele-class action and cohomology can be transported through the
equivalence of the two automorphism groups. Establishing that reduction
is a separate proof obligation; proving the common-universe arithmetic
assertion remains necessary.
