# Tangent dimension bounds from subgroup cells in actual quotients

This internal module works over an arbitrary field `k : Type u`. It relates
the actual dual-number tangent submodule of an all-test subgroup functor to
the dimension of a scheme containing an open cell of its representative.
It assumes the cell and quotient data explicitly.

`RelativeRoot.representedTangentLinearEquiv F j hj` is the canonical
`k`-linear equivalence from `Additive (lieKernel U k)` to
`RelativeRoot.tangentSubmodule F` when `j : U ⟶ G` represents `F` and both
groups are affine. The representing map is monomorphic. Its differential is
therefore injective, and the published exact Lie-image comparison identifies
its range with the intrinsic tangent submodule. The construction composes
the linear equivalence onto that range with this equality of submodules.
`finrank_tangentSubmodule_eq_of_isRepresentedBy` records the resulting
equality of finranks. These two declarations require no smoothness or
finite-dimensionality assumption.

`Lie.finrank_kernel_cast_le_topologicalKrullDim` assumes a smooth affine
group `U`. The published identity-stalk comparison identifies its Lie
finrank, cast into `WithBot ℕ∞`, with the Krull dimension of its identity
stalk. The latter is the coheight of the identity point in the specialization
order. The order isomorphism between scheme points and irreducible closed
sets bounds that coheight by `topologicalKrullDim U.X.left`.

If `c : U.X ⟶ X` is an open immersion, the induced topological embedding
gives `topologicalKrullDim U.X.left ≤ topologicalKrullDim X.left`.
`RelativeRoot.finrank_tangentSubmodule_cast_le_of_openImmersion` combines
this with the preceding two comparisons. Its corollary
`finrank_tangentSubmodule_le_one_of_openImmersion` gives tangent finrank
at most one when `X` has topological Krull dimension at most one.

`QuotientCell.finrank_tangentSubmodule_cast_le` applies this bound to an
actual quotient `q : G.X ⟶ Q`. Its hypotheses are a monomorphic subgroup
map `i : P ⟶ G`, the exact right-coset fiber criterion on every test scheme,
surjectivity, flatness and quasi-compactness of `q`, and an open immersion
of the actual multiplication map `U × P ⟶ G`. The published
`QuotientCell.isOpenImmersion` descends that multiplication cell to the open
immersion `U.X ⟶ Q`, so the intrinsic tangent finrank is bounded by
`topologicalKrullDim Q.left`. No properness or projective embedding is
needed for this implication.

Provenance: these are internal consequences of the published actual
Lie-image, smooth identity-stalk and fpqc cell-descent comparisons, together
with Mathlib's order and topological dimension inequalities. No external
structural assertion is introduced. In particular this module does not
construct a dynamic quotient, prove its properness or dimension at most
one, or prove `RankOnePositiveRootUniquenessStatement`. Those remain
separate obligations for the intended rank-one consumer.
