# Regularity of coefficient norms on the central quotient

`Langlands.CoefficientNormRegularityStatement` asserts continuity of the
actual function `UnitaryCentralCharacter.coefficientNorm` on `G / Z(G)`,
and its almost everywhere strong measurability for every measure when the
quotient has a Borel measurable structure.

The group `G` is any topological group. The representation carrier `V` is
an algebraic complex module with no topology, in a universe independent
of the group's universe. A unitary central-character datum for the actual
representation is supplied. The functional may be any element of the
algebraic dual; only the vector is assumed smooth. Neither admissibility
nor smoothness of the functional or of the whole representation is needed.
The topology is the existing quotient topology on the actual quotient by
the full center, not a separately supplied topology or quotient model.

The measure in the second conclusion is arbitrary. There is no Haar,
sigma-finiteness, or finite-measure hypothesis. The conclusion concerns
measurability, and asserts no finite integral or Lp bound.

## Internal provenance

This is an elementary consequence of the existing
`Langlands.matrixCoefficient_isLocallyConstant` theorem and Mathlib's
quotient-topology and measurability APIs. The smooth-vector theorem makes
the complex matrix coefficient locally constant, hence continuous.
Composition with the complex norm is continuous on `G`.
Its equality with the pullback of `coefficientNorm` along the quotient map
then gives continuity on the quotient. A continuous real-valued function
on a space with Borel measurable structure is strongly measurable, hence
almost everywhere strongly measurable for any measure.

The unitarity and scalar-action fields of the supplied central character
already ensure that `coefficientNorm` is well defined in its published
construction. This statement adds regularity of that same function.
It supplies the measurability premise of subsequent countable-cell Lp
tests, and does not assert any analytic temperedness criterion.
