# Proof of discrete closed actual function-field diagonals

`Langlands.Global.functionFieldAdelesDiscrete` proves the published-object
target `Langlands.Global.FunctionFieldAdelesDiscreteStatement`. Both clauses
range over fields in one arbitrary universe, with compatible `k`- and
`RatFunc k`-algebra structures and `FunctionField k F`. The curve-place
clause retains perfect constants from the existing full-field diagonal;
the absolute-value clause assumes finite constants. No separability,
residue-finiteness, or compactness premise is used.

`isIntegral_of_forall_mem_curvePlace` supplies the arithmetic input, without
requiring perfect or finite constants. If `x : F` integral at every actual
curve place were outside the integral closure of `k` in `F`, the valuative
criterion `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn` would
give a valuation subring `V` containing that integral closure and excluding
`x`. In particular, `V` contains every constant and is proper. The published
`functionFieldPlaceOfValuationSubring` promotes it to an actual curve place:
its principal-ideal property follows from the function-field hypotheses.
The assumed all-place integrality then contradicts exclusion from `V`.
Consequently `x` is integral, and hence algebraic, over `k`.

`eq_zero_of_forall_mem_curvePlace_of_lt_one` adds a strict valuation bound
at any actual curve place. If `x` were nonzero, the existing triviality of
that place's valuation on `k` and
`Valuation.transcendental_of_ne_one` would make `x` transcendental over `k`,
contradicting the proved integrality. Thus global integrality and that one
strict inequality force `x = 0`.

`curvePlaceDiagonalIsolatingSet` is the set of actual curve-place adeles
integral at every place and of valuation strictly below one at
`curvePlaceReference k F`. This reference is an actual place constructed
above the rational-function place at zero; it is available under the given
function-field hypotheses. The everywhere-integral condition is open in
the existing cofinite restricted-product topology by
`RestrictedProduct.isOpen_forall_mem`. The remaining strict ball is open by
`Valued.isOpen_ball`, after converting its restricted value group with
`Valuation.restrict_lt_one_iff`. Its pullback under the continuous reference
coordinate is open. Intersecting proves the isolating set open; zero
belongs to it by the valuation and integer-ring zero laws.

For an actual diagonal element in this set, the published
`curvePlaceCompletion_mem_integers_iff` transfers each completed-integrality
condition to the original place. The adic completion's valuation formula
transfers the strict reference-coordinate bound to the original valuation.
The arithmetic result forces the original field element to be zero. This
proves that the intersection of the isolating set with the subring image of
`curvePlaceAdeleDiagonal k F` is exactly `{0}`.

The induced subspace topology therefore makes the singleton zero open in
the diagonal image. The topological additive-group criterion
`discreteTopology_of_isOpen_singleton_zero` proves
`curvePlaceAdeleDiagonal_discreteTopology`. All actual completed factors are
Hausdorff, so their restricted product is Hausdorff. Applying
`AddSubgroup.isClosed_of_discreteTopology` to the image's additive subgroup
proves `curvePlaceAdeleDiagonal_isClosed`.

For finite constants, `mem_absoluteValueDiagonal_range_iff` identifies the
absolute-value diagonal image with the inverse image of the curve diagonal
image under `functionFieldAbsoluteValueAdeleEquiv k F`. It uses the published
identity `functionFieldAbsoluteValueAdeleEquiv_diagonal`, and injectivity of
the same ring equivalence proves the converse. The existing adelic
homeomorphism consequently restricts to a homeomorphism of the two diagonal
images. Discreteness transfers through this homeomorphism. Closedness
transfers as the inverse image under the continuous adelic equivalence.
These give `realAbsoluteValueAdeleDiagonal_discreteTopology` and
`realAbsoluteValueAdeleDiagonal_isClosed` with the existing actual
absolute-value restricted-product and subspace topologies.

The final theorem combines these two pairs of conclusions, with exactly
the quantified hypotheses and image carriers in the target. This is a
derived proof using the actual published places, completions, diagonals,
and topology comparison. It proves no compactness of an adelic quotient,
model descent, or geometric point-space comparison; the remaining
whole-paper obligations persist.
