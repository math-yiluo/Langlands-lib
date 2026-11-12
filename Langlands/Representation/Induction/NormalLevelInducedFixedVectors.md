# Induced fixed vectors at a prescribed normal level

This internal construction concerns actual smooth induction from a subgroup
`P` of a topological group `G`, over a commutative ring with an independent
coefficient-vector universe.

For an open subgroup `K` and a subgroup `K₀` normalizing `K`,
`normalLevelEvaluation` restricts a `K`-fixed covariant function to `K₀`.
Its values lie in the fixed space of the inducing action under the literal
inverse image `K.comap P.subtype`. Normalization of `K` identifies every
coefficient stabilizer `P ∩ k K k⁻¹`, for `k ∈ K₀`, with this same subgroup.

If every element of `G` is a product of an element of `P` and an element
of `K₀`, covariance makes this evaluation map injective.
If `K` is also compact, its domain is nontrivial exactly when its coefficient
fixed space is nontrivial. In the forward direction injectivity detects a
nonzero value. In the reverse direction the published compact double-coset
section centered at the identity has the prescribed nonzero coefficient.

Neither smoothness nor admissibility of the inducing action is required;
the representation being used is the published smooth part of induction.
There is no closedness assumption on `P`, compact-quotient assumption,
compactness or openness assumption on `K₀`, or requirement `K ≤ K₀`.

This criterion does not assert generation by fixed vectors or visibility of
each constituent. Its provenance is the stated internal evaluation argument
and the published actual compact-section construction.
