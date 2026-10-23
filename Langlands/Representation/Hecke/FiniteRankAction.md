# Finite rank of the admissible integrated Hecke action

`Langlands.Hecke.integratedActionToFixed` factors the existing integrated
test-function operator through the existing fixed-vector submodule. If a
Schwartz–Bruhat function `f` is left invariant under `K` and right invariant
under `J`, it gives a complex linear map from the full representation carrier
`V` to `fixedVectors ρ K`. Composing with the subtype inclusion gives exactly
`integratedAction μ ρ hρ f`. The domain remains the full carrier, unlike the
published corner action, which restricts both input and output to fixed vectors.

The group and representation carrier have independent universes. The group
is a topological group with its Borel measurable structure. The measure is
finite on compact sets and left invariant; no right invariance or normalization
is assumed. The representation is smooth, and its carrier is an algebraic
complex vector space without a topology or a finite-dimensionality hypothesis.
The factorization itself needs no local compactness or admissibility.

The construction uses `LinearMap.codRestrict` and the published
`integratedAction_mem_fixedVectors`. Its evaluation and factorization
identities are definitional. `integratedAction_range_le_fixedVectors`
expresses the resulting inclusion of the whole image in the fixed submodule.

For a Hausdorff, locally compact, totally disconnected group and an admissible
representation, `exists_common_finiteDimensional_fixedVectors` gives a common
finite-dimensional fixed-vector space containing the images of any finite
family of test-function operators. Its compact open subgroup can be chosen
inside any prescribed open subgroup. The proof applies the published
`commonCompactOpenBiInvariance`, then applies the image inclusion to each
function. Admissibility gives finite-dimensionality of these fixed vectors.
This also covers an empty family of test functions.

`integratedAction_finiteDimensional_range` applies that result to a singleton
family. Mathlib's `Submodule.finiteDimensional_of_le` then gives
finite-dimensionality of the actual image. The final
`heckeAction_finiteDimensional_range` restates the result for the published
measure-indexed Hecke algebra action, whose underlying operator is the same.

This is a derived internal construction from the published integrated action,
compact-open common invariance, admissibility, and finite-dimensional subspace
inheritance. It supplies the finite-rank input for a future distribution
character. It defines neither a trace nor a character and proves no
Gelfand–Kazhdan identification or generic contragredient theorem.
