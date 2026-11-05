# Rational corrected support cores

This internal adapter specializes `CorrectedSupportCore` and
`CorrectedSupportComparison` to the existing rational-point subgroups. Its
structural input is the explicit `StandardParabolicPointsStatement`, through
`RationalCorrectedSupportComparison`. This module does not construct an
inhabitant of that statement.

`rankOrderedBaseCellSupport i ν cs j` is the actual rational-point subset
formed by the base-parabolic double cosets with index in the literal
`Support.rankOrderedSupport cs.length j`. Both subgroup factors are exactly
`parabolic i ν ∅`, and the indexing Weyl group is the normalizer of the point
torus modulo its full centralizer. The definition applies at every natural
index, using precisely the existing decreasing-length list and its tie
choices. It requires a finite Weyl group and its decidable equality, but no
points statement, subgroup comparison, topology or finite-simple-root
assumption.

`cellDoubleCosetComparison_of_standardParabolicPoints` restates
`parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints` in the exact generic
`CellDoubleCosetComparison` interface. It compares all actual point-normalizer
representatives and the literal Coxeter subgroups for arbitrary finite subsets
of the actual simple roots.

`cellIndexSeparation_of_standardParabolicPoints` applies that comparison at
two empty root subsets. The theorem `standardSubgroup_empty` identifies both
Weyl subgroups with the trivial subgroup. The witnesses in `DoubleCoset.eq`
are then both the identity, so the two Weyl indices are equal. No nonempty-root
assumption is needed. The ambient Weyl group is still the actual normalizer
modulo the full centralizer.

`groupSupport_eq_twoSidedCore_of_standardParabolicPoints` applies
`CorrectedFiltration.groupSupport_eq_twoSidedCore`. Its base cover comes from
`isBruhatCover_of_standardParabolicPoints` at the empty right subset; its
separation is the preceding deduction. Its parabolic comparison uses exactly
the subgroups at `Finset.univ \ s` and `I`. The published
`standardParabolic_monotone` supplies the two base-subgroup inclusions from
`StandardParabolicOrderStatement`.
The conclusion is equality with the largest actual two-sided parabolic core
of `rankOrderedBaseCellSupport i ν cs j`, for every natural index. Unfolding
that definition gives the base-cell union of the literal
`Support.rankOrderedSupport cs.length j`.

`groupSupport_mul_left_of_standardParabolicPoints` and
`groupSupport_succ_sdiff_eq_of_standardParabolicPoints` apply the corresponding
generic theorems from `CorrectedSupportComparison`. The first gives left
parabolic invariance at every index. The second retains the exact valid list
position, whole-double-coset minimality, and lift of the inverse list entry;
its difference is exactly the set of `p * m⁻¹ * q` with the required actual
parabolic factors. These give the two algebraic conclusions used by the
surviving-support interface, conditionally on the stated points input.

The comparison and core theorems hold over arbitrary fields at universe `u`,
with the connected reductive, maximal split torus, generic cocharacter, point-normalizer and
point-centralizer comparisons, and actual Levi Weyl identification shown in
Lean. The fixed-order deductions additionally use finite ordered simple roots,
a finite Weyl group, its displayed decidable equality, and the order statement.
They require no topology, root-length comparison or positive-simple-reflection
comparison. The provenance is the existing literal cell union, the elementary
empty-subgroup argument and the imported generic support deductions; no
additional literature is used.

Neither fixed-order openness nor any paused structural proposition is proved.
No premise is added to `RationalCorrectedSurvivingSupportStatement`, whose
Lean/Markdown pair and imported pairs are unchanged. In particular, this
conditional adapter does not prove the whole assigned proposition.
