# Negation of actual relative roots from normalizer reflections

Author: Worker 1310.

This module gives conditional adapters for the published actual relative roots.
It does not prove `RelativeRootNegationStatement` without a structural premise.
The field and all group schemes retain the original universe, and no
characteristic, perfectness, reducedness or nonemptiness assumption is added.

The first lemma applies the published normalizer stability of the actual root
set to a normalizing point whose character action negates the given root.
`IsRelativeReflection.neg_mem_relativeRoots` chooses a normalizer representative
of the relative Weyl group element. Its given reflection action negates the
rationalized root. Injectivity of rationalization for a split torus identifies
the character image with the opposite root, so the first lemma applies.

`RelativeRootReflectionData.neg_mem_relativeRoots` instead specializes the given
integral action formula to the root itself. The self-pairing is two, hence the
image is `α - 2 • α = -α`. This proof requires no splitness, finiteness,
generation of the relative Weyl quotient or faithfulness on the root span.
Existence of the reflection data remains an explicit input.

`RelativeRootReflectionData.negEquiv` constructs the opposite-root permutation
of the actual root subtype from these data. Both directions send a character
to its additive inverse; the inverse laws follow from double negation.
`coe_negEquiv_apply` records the character value of this permutation.

Finally,
`relativeRootNegationStatement_of_relativeRootSystemStatement` specializes the
given full structural statement and applies the existing
`HasRelativeRootSystem.neg_mem_relativeRoots` lemma with splitness of the
maximal split torus.

These are internal consequences of the published definitions and lemmas in
`RelativeRoots`, `RelativeReflection`, `RootFiniteness`,
`RootReflectionAssembly` and `RelativeRootStandardCocharacter`. They introduce
no new mathematical existence claim or additional source assertion.
