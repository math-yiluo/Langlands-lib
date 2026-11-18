# Actual formal unit coherence for coefficient extension

This internal unit identifies both actual full-order coefficient-composition
unit maps with the existing actual identity-base comparisons. It proves
equalities of whole integral formal atlas isomorphisms and packages their
rationalized test squares.

`baseComp_left_unit_source` uses the proved source selection through an equal
image cover and the original identity-source equation. Thus iterated and
direct source generators agree when the first coefficient map is the identity.
`baseComp_right_unit_source` applies identity-source equality after extension
for the second coefficient map. These equations allow infinite covers and
coefficient maps merging generators.

`baseCompReAlgebraIso_hom_coordinates` retains the exact original transition
coordinate formula under supplied intermediate and final scalar structures.
The two unit-coordinate equations use the proved source equalities with
`testTransition_coordinates_eq`, then the actual self-transition identity.
This avoids a dependent rewrite of the chart's unit proof.

`Hom.baseChangeAlong_coordinates` retains the complete original formal map
series on the restricted test through extension and scalar retyping. Full
formal-map extensionality and inverse uniqueness then give
`OrderAction.baseAlongCompIso_left_unit`: the left composition unit is actual
extension of the original identity-base comparison. The right unit is the
actual identity-base comparison of the extended action. Neither equation
uses equality of point evaluations.

`baseAlongLeftUnitTestSquare` and `baseAlongRightUnitTestSquare` restrict those
same integral isomorphisms to a specified test chart and package their
rationalized squares, with actual integral identity maps on the remaining
two edges. Both actual rational inverses are retained.

Coefficient and acting rings and the rational field may have separate
universes; the finite coordinate type is arbitrary. Rationalization uses the
existing domain and fraction-field assumptions. This is generic coefficient
unit coherence. Quotient-unit coherence and original framed identity and
composition comparisons, class functor laws and representability remain
subsequent constructions.
