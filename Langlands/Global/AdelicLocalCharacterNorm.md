# Normalized character norms on actual local point groups

Author: Worker 107.

This internal adapter uses the actual completion algebra `placeCompletion F i`
and actual point group `PlaceGroupPoints F G i` of `AdelicGroupLocalPoints`.
The number field has arbitrary universe `u`. No change of carrier, topology,
group operation, or completion norm is made.

The completion and finite-type affine local point groups are locally compact.
For a finite completion, the existing compact valuation ring is an open
neighborhood of zero, which gives local compactness of the additive group.
The archimedean case uses the existing completion instance. Local compactness
of affine points then follows from the existing closed finite-coordinate
embedding. The point group's measurable structure is the Borel sigma algebra
of its existing evaluation topology.

`placeNormValue` applies the existing normalized completion norm to a unit.
At an archimedean place it raises the norm to the existing multiplicity
`w.mult`, one for a real place and two for a complex place; at a finite place
it uses the norm directly. Norm multiplicativity gives a homomorphism, and
norm continuity gives the continuous unit-valued homomorphism `placeNorm`.
The inverse unit supplies its inverse value.

`AdelicGroupPoints.localCharacterNorm` composes this normalized local norm
with actual evaluation of a rational algebraic character. Its continuity
uses the published continuity of character evaluation in the regular-function
point topology. `characterUnits_atPlace` is the published naturality of
character evaluation specialized to the actual adele coordinate map. The two
real-valued local norm formulas follow by taking the unit value.

`coe_characterNorm_eq_prod_localCharacterNorm` identifies the existing
adelic character norm with the product of these local norms: a finite product
at the archimedean places and the finite-support product at the finite places.
It rewrites each factor by the coordinate formula and applies the existing
`IdeleAbsoluteValue.coe_full`. This is a product identity for character norms;
it asserts no Haar modular-character comparison or Haar right invariance.
The local analytic comparison and its assembly on actual adelic points remain
separate proof obligations.

The provenance is internal: all constructions and identities are direct
adapters of the published actual point, completion, normalized idele-norm,
compact completed-integer-ring and affine finite-coordinate infrastructure.
