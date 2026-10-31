# Generic constituent Jacquet comparison and irreducible heads

Author: Worker 166.

`Langlands.glRelativeGenericComparison` proves the exact Library proposition
`Langlands.GLRelativeGenericComparisonStatement.{uF, uV, uW}`. Its two clauses
are also supplied separately as `glRelativeGenericJacquetMultiplicity` and
`glRelativeGenericHead`. The field, fine representation and coarse constituent
universes are independent.

Fix a positive rank, an actual coarse block shape `B` and refinement `S`, and
irreducible cuspidal unitarizable fine data `ω`. The fine real vector `v₀` is
arbitrary and the coarse vector `t` is relatively generic. The test `τ` is the
actual determinant twist with exponents `-v₀` plus the restriction of `t`,
pulled to the actual refined subgroup through `flattenedLeviEquiv`. Write `I`
for its normalized inner induction. For every irreducible admissible actual
subquotient `μ` of `I`, the theorem supplies finite composition series of the
inner and ambient opposite Jacquet modules in which `τ` has the same natural
multiplicity `m`. It proves that `m` is positive exactly when an actual
surjective intertwiner `I → μ` exists. For each such quotient, the outer
induction has an irreducible quotient, and all irreducible quotient maps have
the same kernel, as specified by `Classification.HasIrreducibleHead`.

## Constituent comparison

The proof forms the literal fine twist `α` on the flattened Levi. Real-twist
preservation supplies its irreducibility and cuspidality. The unconditional
`CuspidalSupport.cuspidalInductionLength` and
`refinedCuspidalInductionFiniteLength_of_cuspidalInductionLength` then give
admissibility and an actual finite composition series of `I`. Each grade is
admissible: its upper invariant subspace inherits admissibility by inclusion,
and the grade inherits it through the surjective graded projection.
`UnitaryDualJacquetSupport.levi_compactOpen_cofinal` supplies the compact open
subgroups needed for this quotient argument.

The unconditional `glRelativeGenericJacquetTotals` supplies actual finite
series for both full-induction Jacquet modules with the same total `N`.
That imported theorem uses the product-Levi and GL cuspidal Weyl counts.
Unitarity controls the real exponents of Weyl-equivalent twists; relative
genericity confines their stabilizer to the coarse block Weyl group, and the
restricted and full self-association counts agree. Actual normalized induction
transitivity and flattened opposite Jacquet comparison identify the ambient
module used in the GL count.

`glRelativeJacquetEqualTotalsComparison` applies to the chosen series and
these totals. Its filtration decomposition produces natural inner and ambient
counts at each grade. Actual opposite reciprocity and Jacquet embeddings give
the constituentwise inequalities; equality of the finite sums forces equality
at every grade, including repeated factors. An actual simple subquotient is
equivalent to a grade, and multiplicity transport gives the two actual-series
witnesses for `μ`, without equating its carrier universe with that of `I`.

Finally, `glRelativeInnerJacquetPositiveQuotient` identifies positivity of the
supplied inner count with an inner quotient. Its cuspidal extraction step
turns an actual occurrence of the fine twist into a nonzero map to the inner
Jacquet module; actual second adjointness detects the surjective inner
quotient. Conversely, such a quotient gives a nonzero map and a positive
actual count. Thus neither count existence nor positivity is a new premise.

## Head consequence

A surjective map `q : I → μ` presents `μ` as a subquotient by using the full
invariant subspace. The constituent theorem gives equal counts, and its
quotient criterion makes their common value positive.

`normalizedParabolicInduced_refined_finiteLength` gives finite length of the
outer induction of `I` from the same unconditional cuspidal induction length
theorem. Actual normalized induction carries `q` to a surjection, using
smooth induction surjectivity. Finite length therefore passes to the outer
induction of `μ`.

`glRelativePositiveTotalHead` now applies with the equal positive counts and
that finite length. In this imported theorem, nonvanishing and finite length
supply an irreducible quotient. Second adjointness, Jacquet exactness and
normalized transitivity bound its actual Jacquet count below by `m`. Distinct
irreducible quotient kernels would give a quotient onto the direct sum of
the two targets, even when those targets are isomorphic. Additivity would
force a count at least `2m` inside total `m`, contradicting positivity. This
proves the stated uniqueness of kernels.

## Provenance and scope

This proof assembles published Library results; the assembly was developed by
Worker 166. The source and derived scope are those of
`RelativeJacquetMultiplicityStatement.md`: A. J. Silberger, *The Langlands
Quotient Theorem for p-adic Groups*, Mathematische Annalen 236 (1978), 95–104,
Lemma 5.3 on p.100 and Lemma 5.5 on pp.100–101. The registered original is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.

The proof retains the actual constituent restriction documented in
[the scope audit](../../../notes/jacquet/silberger-lemma53-scope.md). It derives
the arbitrary-`v₀` generic statement using published totals and extraction,
without an intermediate discrete-series support condition or a chamber
inequality. All-regular continuation, supported recovery and cosocle
multiplicities are separate results. The target pair and its import closure
are unchanged; the theorem adds no hypothesis or axiom.
