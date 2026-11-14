# Compact pro-p unipotent factors of apartment chamber fixers

This internal specialization works over a nonarchimedean local field at an
arbitrary universe, with the canonical topology on the original rational-point
group. The supplied KP datum satisfies its single-group axioms.

The actual pointwise zero fixer of every facet equals the integral-point image
of its neutral model, so it is compact. For an apartment chamber, the setwise
zero stabilizer equals this facet fixer. Its intersection with the closed
actual dynamic unipotent point group is therefore compact. This proves
`isCompact_chamber_unipotent_factor` for every cocharacter, without genericity.

The actual dynamic group is a closed represented unipotent subgroup of the
connected reductive ambient group. Its finite-type hypothesis follows from
ambient smoothness. The compact dynamic-unipotent subgroup theorem consequently
proves `isProP_chamber_unipotent_factor` for the characteristic of the actual
residue field. The subgroup and its inherited topology are unchanged.

For a generic cocharacter, applying this result to both it and its negative
discharges the two explicit pro-p hypotheses in the chamber split construction.
`chamberPositiveCentralizerDecomposition` chooses actual positive and
centralizer-zero factors of every chamber fixer element and retains their
literal multiplication identity. The companion `chamber_normalizer_eq` proves
the normalizer identity inside the original zero subgroup for apartment
chambers, using the previously proved split Tits-system theorem.

The provenance is internal: neutral-model integral-point compactness, closedness
of the actual dynamic points, the compact-unipotent pro-p theorem and the chamber
split construction are composed directly. This pair establishes the chamber
factor input and its immediate normalizer consequence; the full available-data
maximal-pro-p proposition additionally requires its other clauses and transport
to all building chambers.
