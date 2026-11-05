# Cell boundary length from simple parabolic products

This internal module derives strict Coxeter length decrease on actual
base-cell boundaries from a compact base quotient, closed monotone
parabolics, the base-cell cover, and parabolic double-coset comparisons.
It then proves the full generic fixed-order surviving-support target.
It asserts no unconditional rational-point instance.

`parabolicWordSet` is the product of the simple parabolics in a word, followed
by the base subgroup. The group and simple-index types have independent
universes. Monotonicity makes this subset invariant under both base
actions (`parabolicWordSet_base_invariant`). Under the locally compact
nonarchimedean group hypotheses and compactness of
`Induction.LeftQuotient (P ∅)`, compact right representatives reduce
multiplication by a simple parabolic to multiplication by a compact set.
The representatives come from
`exists_compact_right_representatives_of_compact_quotient` in
`CorrectedSupportOpenness`. The Mathlib theorem
`IsClosed.mul_left_of_isCompact` then proves
`isClosed_parabolicWordSet` by induction.

The algebraic arguments use
`CellDoubleCosetComparison T (P J) (P ∅) (standardSubgroup cs J) ⊥`
for every finite subset `J`. Comparing a normalizer lift with the identity
shows that any lift whose index belongs to `standardSubgroup cs J`
belongs to `P J`. Choosing lifts of the simple reflections and factoring
a lift of a word product proves `cellSupport_wordProd_subset`, including
the empty word. No choice of representatives changes the cell definition,
which still uses all lifts in the full-centralizer quotient.

For the converse bound, the cover expresses a point of a simple parabolic
times the cell of `v` in some cell of `v'`. The comparison places `v'`
in `standardSubgroup cs {a} * v`. Subgroup closure induction and
`cs.simple_mul_simple_self` show that this singleton-generated subgroup
contains only the identity and `cs.simple a`. Thus the new index is
either `v` or `cs.simple a * v`.

`parabolicWordSet_index_bounds` inducts over the word. The Mathlib
inequality `cs.length_mul_le` and identity `cs.length_simple` bound
every resulting cell index by the number of letters. Equality forces the
simple reflection at every step and therefore forces the index to be
`cs.wordProd ω`. This conclusion does not require the word to be reduced.

`cellBoundaryRank_of_parabolicComparisons` chooses a reduced word for `w`
using `cs.exists_isReduced`. Its closed word product contains the entire
cell of `w`, so also its closure. The preceding bound applies to any point
of that closure. If its cell index had the original length, it would be
`w`, contradicting exclusion from the original cell. The boundary
therefore belongs to a strictly shorter cell, exactly as required by
`CellBoundaryRank T (P ∅) cs.length`.

Finally, `survivingSupportTarget_of_parabolicComparisons` assumes the
comparisons for all parabolic pairs, derives base-index separation from
the empty/empty comparison, and applies
`survivingSupportTarget_of_cellGeometry`. This gives both consecutive
open supports, left parabolic invariance, and the exact surviving
difference through the original `SurvivingSupportTarget`. The
implemented decreasing-length list, every choice among ties, the largest
two-sided cores and the inverse-lift convention are retained literally.
Finite ordered simple indices and the existing finite decidable Weyl
quotient are required only for this final specialization.

The provenance is internal: the new deductions are elementary group,
finite-word and topological arguments built on the existing Library
interfaces and Mathlib Coxeter results. No additional literature
assertion or Tits-system axiom is assumed. The actual rational cover,
parabolic comparisons and quotient compactness remain to be proved or
supplied by other results; this conditional supporting unit does not
prove `RationalCorrectedSurvivingSupportStatement`. The exact rational
target and all its imported Lean/Markdown pairs are preserved.
