# The canonical rational component regular representation

For an affine group scheme `G` locally of finite type over an algebraically
closed field, its canonical rational-point quotient by the rational identity
kernel is finite. The construction `componentRegularRepresentation` supplies
an actual regular matrix representation in a chosen finite coordinate
dimension. The canonical quotient is constant on actual components because
its embedding into the actual component type is injective.

The theorem `not_dvd_card_componentPointQuotient_of_linearlyReductive` applies
the preceding finite-quotient obstruction. If every actual representation is
semisimple in the exact all-test sum-of-simple-subspaces sense, characteristic
`p` does not divide the quotient order. The next theorem expresses this as
nondivisibility of the number of actual connected components.
Neither theorem assumes smoothness or reducedness.

For an arbitrary base field, the final theorem identifies the geometric
component cardinal in Nagata's statement with the rational quotient cardinal
after algebraic closure. It requires linear reductivity of that base-changed
group as an explicit hypothesis. Preservation of linear reductivity under this
extension is not proved here and is not inferred from Nagata's theorem.
Thus this module does not prove the full arbitrary-ground-field
component-order necessity.

This is internal derived infrastructure. The canonical rational
component quotient and stable-complement modules are reused unchanged.
The actual regular representation, its componentwise-constant algebraization,
and the order obstruction build on `FiniteComponentQuotientRegular`.

The source motivation is J. S. Milne, *Algebraic Groups*, corrected reprint
(2022), Proposition 2.37, printed p.51 (PDF p.62), for geometric component
cardinality; Definition 4.15 and Proposition 4.17, printed p.90 (PDF p.101), for
the semisimplicity convention; and Remark 12.56, printed p.249 (PDF p.260), for
the order obstruction. The source is registered as
`milne-2022-algebraic-groups`. The complete official errata snapshot registered
as `milne-2022-algebraic-groups-errata-2026-11-04` warns about rational
representatives over a separable closure on p.51; all component representatives
used here are over an algebraically closed field.
