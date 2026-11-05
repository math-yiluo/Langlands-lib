# Fixed-order corrected support from actual cell geometry

This internal deduction proves a conditional version of the exact four-field
`SurvivingSupportTarget` for the existing support implementation. It does
not prove `RationalCorrectedSurvivingSupportStatement` or add premises to
that proposition. All existing target and imported pairs are preserved.

`CellBoundaryRank T B rank` is a proposition about the supplied topology
on the actual group. Every point of
`closure (cellSupport T B B {w}) \ cellSupport T B B {w}` must belong to
some base cell of strictly smaller rank. The definition proves no instance
of this condition.

`isOpen_cellSupport_of_rank_upper` assumes a finite Weyl quotient, a cover
by base cells, `CellIndexSeparation`, this boundary condition, and an index
set containing every strictly higher rank than any of its members. The
proof takes the union of the excluded cells. Closure commutes with this
finite union. A boundary point of an excluded cell belongs to a cell of
strictly smaller rank, which is also excluded by the rank-upper condition.
The excluded union is therefore closed. Index separation and the base-cell
cover identify its complement with the desired support. Equal-rank cells
may be included in any order.

`exists_compact_representatives_of_compact_quotient` works for a locally
compact nonarchimedean group. For a base subgroup `B` whose actual left
quotient `Induction.LeftQuotient B` is compact, it obtains a compact open
subgroup from `compactOpenSubgroupBasis`. The published
`Induction.exists_finset_doubleCoset_cover` gives finitely many `B i K₀`
covering the group. The union of the translates `i K₀` is compact. Its
intersection with any closed subgroup `P` containing `B` gives compact
left base-coset representatives inside `P`.
`exists_compact_right_representatives_of_compact_quotient` inverts those
representatives to obtain the right-hand version. These are deductions
from compact quotient hypotheses, not proofs of rational quotient
compactness.

`isOpen_groupSupport_of_cellGeometry` uses the exact identity
`groupSupport_eq_twoSidedCore`. It first applies
`Support.rankOrderedSupport_isRankUpper` and the finite-boundary argument
to the literal prefix `Support.rankOrderedSupport cs.length j`. It then
uses the compact representatives just constructed and the published
`Support.isOpen_twoSidedCore_of_compact_representatives` to make the
largest actual parabolic core open. The latter theorem is generic in
`CorrectedSupportTopology`; that module also imports GL developments,
but no GL specialization is applied here. This route makes no assertion
that a modified Weyl support is itself rank upper.

`survivingSupportTarget_of_cellGeometry` assembles the exact four fields
for every valid position and inverse normalizer lift. Both consecutive
supports are open by the preceding theorem. Left invariance uses
`groupSupport_mul_left_of_doubleCosetComparison`, and the single actual
double-coset difference uses
`groupSupport_succ_sdiff_eq_of_doubleCosetComparison`. These retain the
literal decreasing-length list and its tie choices, the largest two-sided
cores, and the order `p * m⁻¹ * q` in the target.

The assembly retains the following inputs explicitly: monotonicity and
closedness of the parabolic family, compactness of the base left quotient,
the actual base-cell cover, index separation, the normalizer double-coset
comparison for all parabolic pairs, and strict boundary length drop in the
actual topology. It supplies no rational instance of the cover, separation,
comparison, compactness or boundary condition. Its provenance is this
finite topological and elementary group argument, using the named imported
Library results. No new literature or external structural assumption is
introduced into the exact rational proposition.
