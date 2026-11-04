# Actual arithmetic and function-field local compactness

`Langlands.Global.functionFieldAdelesLocallyCompact` proves
`Langlands.Global.FunctionFieldAdelesLocallyCompactStatement`. The fields
`k` and `F` lie in one arbitrary universe; `k` is finite, and the given
compatible `k`- and `RatFunc k`-algebra structures satisfy `FunctionField k F`.
No separability or local compactness premise is used.

`curvePlaceCompletionResidue_finite` first applies
`functionFieldPlaceResidue` to the actual residue field of each
`v : AlgebraicCurve.Place k F`. Its finite dimensionality over the finite
constant field gives a finite underlying type, by `Module.finite_of_finite`.
The canonical `curvePlaceCompletionResidueEquiv` transfers finiteness to
`IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)`.

`curvePlaceCompletionIntegers_compactSpace` uses
`Valued.isClosed_valuationSubring` to give the completed integer ring its
complete subspace uniform structure. Its discrete valuation ring structure
comes from the existing adic-completion instances. The completed valuation is
rank one: `Valuation.IsRankOneDiscrete.rankOne` supplies the rank-one
instance using the real base `2 > 1`. The proof applies
`Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
to the complete integer ring, its discrete valuation ring structure, and
its finite residue field. This proves compactness for the existing topology
on the actual completed integer ring.

`curvePlaceCompletion_locallyCompactSpace` views that compact integer ring
as a compact subset of the completed field. It is open by
`Valued.isOpen_valuationSubring` and contains zero, so it is a compact
neighborhood of zero. The topological additive group criterion
`IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup` then proves local
compactness of the actual completed field.

`curvePlaceAdeles_locallyCompactSpace` supplies compactness and openness of
the actual completed integer ring at every actual curve place.
Mathlib's restricted-product instance then proves local compactness of
`CurvePlaceAdeleRing k F` with its existing cofinite restricted-product
topology.

The final theorem transfers local compactness through
`functionFieldAbsoluteValueAdeleHomeomorph k F` to
`RealAbsoluteValueAdeleRing k F`. The already proved openness of
`curvePlaceAdeleLevel k F S` and `realAbsoluteValueAdeleLevel k F S` gives
local compactness of every finite level in its existing subspace topology.
Together with the preceding compact-integer and local-field conclusions,
these are exactly the conjunctions in the target statement.

This derived proof uses actual arithmetic residue finiteness and an actual
completed-residue comparison; those properties are proved dependencies,
rather than inputs to a conditional local-field package. It proves no
compactness assertion for a whole finite level and makes no assertion about
diagonal discreteness, model descent, or geometric point spaces.
