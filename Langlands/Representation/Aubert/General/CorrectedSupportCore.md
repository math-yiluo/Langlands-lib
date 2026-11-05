# Actual two-sided cores of corrected Weyl supports

This internal algebraic deduction imports `CorrectedSupportComparison` and
preserves the existing corrected support implementation and rational target.
`CellIndexSeparation T B` says that two normalizer elements in the same
actual `B`–`B` double coset have the same class in the existing full-centralizer
Weyl quotient. It supplies no instance for arbitrary subgroups.

`normalizer_mem_cellSupport_iff` uses this separation to recover the index
of a normalizer element from membership in any base-cell union.
`cellSupport_base_invariant` proves that every such union is invariant on
both sides by `B`, directly by multiplying the factors in a cell expression.

`twoSidedCore_cellSupport` identifies the largest actual `P`–`Q` invariant
subset of `cellSupport T B B θ` with
`cellSupport T B Q (Support.twoSidedCore H K θ)`. Its hypotheses are
`B ≤ P`, `B ≤ Q`, a cover by actual `B n B` cells, base-cell index
separation, and the exact `P`–`Q` normalizer comparison
`CellDoubleCosetComparison T P Q H K`.

For the forward inclusion, the proof expresses a point in a base cell.
Every Weyl element in the double coset of its index has a normalizer lift;
the comparison puts that lift in the original point's actual parabolic
double coset. The actual core condition then gives base-support membership,
and separation recovers membership of the Weyl index in `θ`.
For the reverse inclusion, every point of the actual parabolic double coset
has a base-cell expression. The comparison puts that cell's Weyl index in
the original index's Weyl double coset, and the Weyl core condition gives
its membership in `θ`.

`groupSupport_eq_twoSidedCore` specializes this identity to the exact
`Support.rankOrderedSupport cs.length j`, for every natural index `j`.
It retains the implemented tie choices and the literal largest two-sided
core. It does not assert that a corrected Weyl core is rank upper.

The provenance is the elementary group and quotient argument implemented
here and the imported Library definitions. No additional literature is
used. These are conditional algebraic intermediates: they prove no rational
cover, separation or normalizer comparison, no openness statement, and no
instance of `RationalCorrectedSurvivingSupportStatement`.
