# Square-integrable non-induction over the given characteristic-zero field

`Langlands.BaseChange.squareIntegrableNotInduced` proves the full Library
proposition [`SquareIntegrableNotInducedStatement`](SquareIntegrableNotInducedStatement.md)
with independent field and representation-carrier universes. For the given
characteristic-zero nonarchimedean local field `F`, there is no equivalence
of the irreducible square-integrable representation `π` of `GL_n(F)` with
the unnormalized induction of any smooth representation of the Levi of a
standard block parabolic with at least two blocks. As in the statement,
both representation carriers here are in the same universe. The proof
of the bundled version allows those two carrier universes to be independent.

The proof applies
[`CharZeroLocalField.topologicalData`](../LocalField/CharZeroPadicRealization.md)
to `F`. This packages `F` as a `PadicField` at its residue characteristic
with the *same* field, carrier, topology and valuative relation. The
`JacquetLanglands.IsSquareIntegrable` hypothesis is definitionally the
`TopologicalData.IsSquareIntegrable` hypothesis for these data. Both test
square integrability modulo the center for every Haar measure on the same
central quotient with its Borel structure. The smooth Levi representation
and the induced representation in the conclusion also use the same groups,
topology and unnormalized induction. Thus Lean directly applies
[`isEmpty_equiv_smoothInduced_of_squareIntegrable`](PadicSquareIntegrableNotInduced.md)
with no replacement of any group or representation by a model up to
isomorphism.

This is the internal specialization of the bundled-field proof of the
classical non-induction fact, using the characteristic-zero
field adapter `CharZeroLocalField.topologicalData`. The paired bundled-field proof describes the use of
Casselman's criterion and duality. There is no pseudo-coefficient premise
in this theorem.
