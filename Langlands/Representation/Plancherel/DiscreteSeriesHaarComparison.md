# Haar comparison on Borel quotients

These lemmas derive a measure comparison for `IsDiscreteSeriesClass` from
Haar uniqueness and the Library's scalar invariance theorem.

`isDiscreteSeriesClass_haar_iff` works on a locally compact second countable
quotient by a central subgroup, with its Borel measurable structure.
`Measure.isMulLeftInvariant_eq_smul` identifies the second Haar measure with a
scalar multiple of the first, and
`Measure.haarScalarFactor_pos_of_isHaarMeasure` gives strict positivity.
Substituting the scalar multiple reduces the equivalence to
`isDiscreteSeriesClass_smul_measure_iff` on the same smooth-dual class.

`isDiscreteSeriesClass_borel_quotient_eq_iff` first substitutes the equality
of the two central subgroups. `BorelSpace.measurable_eq` identifies each
supplied measurable space with the Borel structure of the common quotient
topology, so a second substitution puts both measures on that one measurable
space. Mathlib's quotient instances pass local compactness and second
countability from the ambient group to the quotient, where the first lemma
applies.
