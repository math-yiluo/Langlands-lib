# Unscaled face weights on actual split root charts

This derived unit gives the actual regular split-cell chart a second weight
family coming from an integral linear form on the root span. Its values on
the chosen positive roots must be nonnegative. The values are used without
rescaling, and zero weights are allowed.

`commutator_unipotent_rootFactor_le_of_rootSpanLinear` realizes a positive
multiple of the linear form by a coordinate cocharacter using
`exists_coPairing_eq_rootSpanLinear`. The existing independent-cocharacter
commutator theorem gives supported coordinates for the actual commutator.
Multiplication by the positive integer preserves strict inequalities, so
coordinates below the original unscaled sum of weights vanish. Each remaining
factor lies in the required height subgroup on every scheme test.
`positiveCellRootLinearWeightData` records the resulting actual `RootWeightData`
on the specified regular-cell chart.

`faceHeight_nonneg_of_isPos` proves that the existing integral face height is
nonnegative on the positive roots of a finite root datum by induction using
simple roots and addition.
`faceHeight_pos_iff_of_nonneg` says that, for a dominant face coweight and a root
with nonnegative original pairing, its face height is positive exactly when that
pairing is positive. It uses the existing vanishing and positive lower-bound
lemmas.

`positiveCellRootFaceWeightData` specializes the linear weight construction to
these face heights. Thus its natural weights count the simple roots outside the
zero-root face, with multiplicity. They depend on the based face and retain the
specified root labels and original order. The auxiliary extending cocharacter
and its positive multiplier do not appear in these weights.

`RootWeightData.subgroup_zero_eq_of_zero_iff` proves equality of the all-test
positive terms for any two weight data on one chart having the same zero roots.
It follows from the exact supported-coordinate criterion. This unit does not
claim compatibility under different maximal tori or base descent.

Provenance is the existing independent-cocharacter commutator construction,
the new positive-multiple lattice realization, the existing face-height
lemmas, and the existing supported-coordinate description of positive terms.
