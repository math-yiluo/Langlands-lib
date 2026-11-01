# Native endomorphism rank in relative dimension zero

This internal proof implements the section argument described by
`SmoothProperConnectedZeroDimensionalRankStatement`.

The helper `isIso_of_connected_separated_etale` works over a separably
closed field. A point of the nonempty connected source lifts the identity
of the field spectrum through the actual etale structure morphism, by
Mathlib's `Scheme.exists_fac_of_etale_of_isSepClosed`. Its lift is an
actual section. The etale diagonal is an open immersion; the general
base-change criterion for cancellation of morphism properties therefore
makes the section an open immersion. Separatedness similarly makes it a
closed immersion. Its nonempty image is open and closed in the connected
source, hence is the whole source. A surjective open immersion is an
isomorphism, and the section identity makes the structure morphism an
isomorphism as well.

The main theorem uses the native equivalence of relative-dimension-zero
smoothness and etaleness. Properness supplies separatedness, and
geometric connectedness over the singleton field spectrum supplies a
connected nonempty source. Algebraic closure supplies separable closure.
Cancellation against the now invertible actual structure morphism
identifies each over-endomorphism with the actual identity. Finally,
`Scheme.Hom.finrank_eq_one_of_isIso` computes native rank as one. No
numerical degree or replacement scheme enters the comparison.

This proves the dimension-zero interface in arbitrary characteristic.
It does not prove the positive-dimensional polarized-rank formula.
