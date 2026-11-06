# Recovery from actual relative graph families

Author: Worker 1656.

This internal construction develops the inverse direction of the actual
relative graph construction over an arbitrary scheme in universe `u`.
It reuses `GraphBaseChange`, actual subgroup ranges and uniqueness of
representatives. No representability existence assertion is assumed.

The subgroup-family lemmas `familyHom_comp` and `evaluate_iso_comp` state
that reparametrizing the source commutes with pullback, and that an
isomorphic source gives exactly the same evaluated subgroup functor.
Their proofs use functoriality of actual pullback and invariance of
all-test subgroup ranges under precomposition by an isomorphism.

The relative graph inclusion is monic because the ordinary graph is monic
and the product comparison is an isomorphism. It represents its range.
`relativeGraph_injective` uses membership of the first graph inclusion
in the second range. The first projections force the resulting source
map to be the identity; the second projections identify the two relative
homomorphisms. All schemes over the parameter base are available as tests.

For an actual inclusion `j : K → (H × G)_M` with invertible first
projection `p : K → H_M`, `homOfRelativeGraphRepresentative j` is
`p⁻¹ j` followed by the second projection. Its graph inclusion is exactly
`p⁻¹ j`; comparison of the two product projections proves this equality.
Consequently `j` factors through the recovered graph by `p`, and its
all-test subgroup range equals that graph.

Conversely, a monic representative whose range equals an actual relative
graph has invertible first projection. Uniqueness of representatives
gives an isomorphism from `K` to `H_M`, compatible with the inclusions.
Composing that compatibility with the first projection identifies the
first projection of `j` with this isomorphism.

The first projection of `familyHom j a` is the pullback of `p` followed
by the source comparison `Descent.pullbackComparison`; this follows from
naturality of that comparison. It remains invertible when `p` is
invertible. Finally,
`evaluate_eq_relativeGraph_evaluate_homOfRepresentative` rewrites `j`
as `p` followed by its recovered graph inclusion, removes the pulled-back
isomorphism from the range, and applies the graph/evaluation identity of
`GraphBaseChange`. Thus the evaluated subgroup is literally the graph
of the evaluated recovered homomorphism on every test scheme.
