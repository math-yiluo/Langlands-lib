# Assembling coherent comparisons from unique normalized representatives

Worker 561.

This internal reduction does not prove existence of pinned normalization or
`RelativePinnedComparisonExistenceStatement`. It specifies a sufficient input
and constructs a `RelativePinnedComparison` from that supplied input.

For arbitrary affine pinned models and arbitrary common schemes,
`AffinePinnedModel.HasUniqueNormalizedComparisons P` says that every class for
`IsFppfInnerEquivalent` contains exactly one comparison satisfying the supplied
predicate `P`. The predicate is data; no geometric interpretation or existence
proof is inferred from its name.

`RelativePinnedNormalization` bundles such a predicate and its unique
representatives, stability under identities, composition and arbitrary
`pullComparison`, and the exact torus and positive-coroot cocharacter
preservation equations of the target. Constructing this structure, including
its uniqueness and stability laws, remains an obligation of any application.

`RelativePinnedNormalization.correction` chooses the unique representative.
Uniqueness proves that correction depends only on the local-inner class,
preserves identities and composition, and commutes with arbitrary
`pullComparison`. For the last property, the module first proves that inner
equivalence is preserved by direct comparison pullback, including the
`baseChangeCompIso` identifications at both endpoints.

Finally, a local-inner discrepancy gives a unique section of every supplied
full-centre fppf quotient with every supplied compatible conjugation action,
by `IsFppfLocallyInner.existsUnique_adjointPoint`. These sections and the
normalization's geometric properties construct `toRelativePinnedComparison`.
The theorem `relativePinnedComparisonExistence_of_normalization` therefore
proves the unchanged target conditionally on the supplied normalization data.

All statements and constructions are derived from the local-innerness
calculus, actual comparison pullbacks, and uniqueness of representatives.
They apply in every universe and impose no affineness, connectedness or
nonemptiness assumption on the common schemes or refinements.
