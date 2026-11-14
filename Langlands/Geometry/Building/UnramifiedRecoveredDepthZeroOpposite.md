# Depth-zero opposite factors from recovered nearby parabolic models

This internal reduction proves that the unchanged
`UnramifiedFixedDepthZeroOppositeStatement` follows from recovered singleton
fixer models with nearby parabolic root comparisons and the separate
`IntegralOppositeFactorsStatement`. It works at arbitrary universe `u`.
Neither input proposition is proved here.

`UnramifiedFixedRecoveredParabolicModelsStatement` uses the field, group,
maximal lower split torus, upper torus, factorization, maximal upper split
torus, opposite factor pairs, upper KP apartment, centralizer and V6
compatibility in the target. At each coefficient-fixed upper apartment
point `z`, it asks for actual lower and upper relative-component models
`L` and `E`, compatible unramified recovery, and equality of the upper
full integral-point image with the character-valuation kernel intersected
with the full pointwise fixer of `{z}`. It additionally asks for
`ParabolicRootComparisonsNearDescentTranslations` for `L` at `z`. That
predicate supplies nearby actual source models and comparisons with
parabolic neutral special-fibre image, exact parabolic reduction preimage
and the forward integral-root bound at the translated point.

The availability statement requires neither a supplied integral torus nor
a supplied special-fibre quotient, and no equality between positive depth
and radical membership. In particular it does not require a proof that
every positive-depth root point reduces into the radical. The nearby
root-comparison input can be obtained from one-sided upper full-fixer
bounds using the recovered-model adapter in
`UnramifiedFixerModelComparison`.

`UnramifiedRecoveredDepthZeroOppositeReductionStatement` is the implication
from this availability statement and `IntegralOppositeFactorsStatement`
to the exact published depth-zero target.
`unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels` proves it
as follows.

1. Upper connected reductivity follows from the lower connected reductive
   group by the published algebraic-extension ascent theorem.
2. Full recovery and the full fixer equality construct the actual closed
   split integral torus in `L.neutral`, by
   `exists_closedSplitIntegralTorus_of_fullRecovery`. The actual reductive
   special-fibre quotient is constructed by
   `SpecialFibreQuotientData.exists_isReductiveQuotient`; the residue field
   of the nonarchimedean local field is finite and hence perfect.
3. A lower root point of restricted value zero is neutral integral by
   `mem_neutral_integralPoints_of_nonnegative_restrictedDepth`. The nearby
   parabolic comparisons exclude it from the actual radical preimage, by
   `not_mem_positivePoints_of_eq_zero_of_parabolicRootComparisons`.
4. The integral opposite-factor input makes both given opposite root
   factors neutral integral. Root negation identifies their occurring
   opposite root. The forward recovered root-integrality comparison gives
   nonnegative restricted depth for each factor.

The proof preserves the original restricted root functions and every
quantifier and hypothesis of the target. Fixedness is used to obtain the
models from the availability input. The provenance is internal composition
of the named Library results and the focused supporting model, integrality
and nearby-comparison lemmas. Actual model existence, the nearby
parabolic-image and exact-preimage properties, and the integral
opposite-factor input remain separate obligations. This is a proved
conditional reduction, not an unconditional proof of the host task.
