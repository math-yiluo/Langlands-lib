# Actual support comparisons from normalizer double cosets

This is an internal algebraic deduction for the corrected Aubert support
filtration. It imports the existing `CorrectedFiltration` implementation and
does not change its definitions or the rational surviving-support target.

`CellDoubleCosetComparison T P Q H K` states that two actual normalizer
elements have the same `P`–`Q` double coset exactly when their images in
`N_G(T)/Z_G(T)` have the same `H`–`K` double coset. The full centralizer is
the denominator already used by the Library. This definition supplies no
instance of the comparison and asserts nothing for arbitrary subgroup
families.

Assuming this comparison, `B ≤ P`, and the actual cover by `B n Q`,
`mem_cellSupport_iff_of_mem_parabolicDoubleCoset` identifies membership in
an invariant cell union with membership of its Weyl index. The proof compares
both normalizer representatives through their common actual double coset.
It then uses the stated Weyl invariance. Its reverse direction uses the
cover to express the original point in the implemented cell union.

The following deductions prove left parabolic invariance, compatibility
with differences whose lower Weyl support is invariant, and the identity
between the union indexed by one whole Weyl double coset and one actual
parabolic double coset. None uses topology or representation coefficients.

`groupSupport_mul_left_of_doubleCosetComparison` applies these deductions
to the Library's actual modified supports, using
`Support.modifiedRankSupport_invariant`.
`groupSupport_succ_sdiff_eq_of_doubleCosetComparison` uses
`mem_modifiedSupport_succ_iff` and
`Support.modifiedRankSupport_succ_diff` for the exact existing
`Support.rankOrderedList cs.length`, including its tie choices.
The class of `m⁻¹` is the new list entry because the assumed class of `m`
is its inverse. The resulting difference has precisely the order
`p * m⁻¹ * q` used by `SurvivingSupportHypotheses.sdiff_eq`.

These theorems are conditional algebraic intermediates. They do not prove
the rational normalizer comparison, the rational Bruhat cover, either
openness field, or the whole
`RationalCorrectedSurvivingSupportStatement`. Their provenance is the
elementary group-theoretic argument implemented here, using the imported
Library support and Coxeter results. No additional literature or external
mathematical premise is introduced into the rational target.
