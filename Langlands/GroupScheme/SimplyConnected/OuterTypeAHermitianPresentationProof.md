# The all-test Hermitian presentation of outer type-A groups

Authors: Worker 239 and Worker 5375.

`Langlands.GroupScheme.outerTypeAHermitianPresentation` proves the exact
published `Langlands.GroupScheme.OuterTypeAHermitianPresentationStatement.{u}`
at every universe `u`, with no additional premise.

The proof applies
`outerTypeAHermitianPresentation_of_specialLinearTitsCocycle`, imported from
`Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianPresentationReduction`,
to the unconditional theorem `specialLinearTitsCocycle`, imported from
`Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleProof`.
The latter proves `SpecialLinearTitsCocycleStatement.{u}` and discharges the
reduction's sole premise at the same universe.

The reduction starts with the finite Galois special-linear presentation and its
matrix discrepancy formulas and split-torus characters. It embeds the actual
quadratic star field into the cover and uses the distinguished first endpoint
to obtain Hermitian coordinates. After correcting the local presentation, the
discrepancy is trivial over the star field and has the inverse-Gram outer
formula over the base field. All-test descent then constructs the natural
family of injective matrix homomorphisms whose image is exactly the
determinant-one isometry group of the nonsingular Hermitian Gram matrix.
The star-field fixation equivalence, Hermitian equation, unit determinant,
diagonal split-torus formula and adjacent-root restrictions supply the
remaining clauses of the target.

This composition retains arbitrary fields in every characteristic, including
characteristic two, every natural number `n`, the actual `TitsIndexData` and
all relative test schemes. The target's outer star-image hypothesis itself
forces `n ≥ 2`; no rank premise is added. The original maximal split torus,
characters, root restrictions and natural coefficient maps are retained.

The provenance is composition of the two published internal results named
above; their paired Markdown explains the constructions and source context.
This proof uses no downstream rank-one classification or Kneser–Tits theorem.
