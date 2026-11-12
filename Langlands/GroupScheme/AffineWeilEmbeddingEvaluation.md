# Original Weil-product coordinates as evaluation pullbacks

Author: Worker 166. Internal construction and point comparisons, derived from
published affine-point naturality and actual pullback projections. No new
external mathematical assertion is used.

The base rings `k`, `K`, and `Ω` are arbitrary commutative rings with the supplied
`k`-algebra structures. For an `Ω`-algebra `R` and a `k`-algebra embedding `τ`,
`embeddingCoefficientRestriction` is the identity ring map from `R` with its
original `k`-action to the conjugate coefficient algebra. The algebra condition
uses `τ.commutes`. Tensoring this restriction with `K` and following it by
`evaluationCoefficientMap` gives exactly `tensorEmbeddingEvaluationMap`; this
comparison uses finite embeddings and the supplied bijectivity of canonical
embedding evaluation where those tensor evaluation maps require it.

For an arbitrary group scheme `W` over `k`, `embeddingIntermediatePoint` is the
actual point over conjugate coefficients obtained from the intermediate pullback
projection. Its underlying scheme map and restriction back to the original
base are proved by the two pullback projection identities.
`evaluationComponent_embeddingPoints` compares the pullback of any supplied
map `W_K → H` with that intermediate point followed by the original map.
`embeddingFactor_component_eq` records generic affine-test extensionality for
one factor coordinate.

For `H` affine and locally of finite type over `K`, with `K` finite projective
over `k`, the remaining lemmas specialize these constructions to the published
actual Weil restriction. `embeddingIntermediatePoint_tensor` follows from the
restriction identity and `pointsEquiv_naturality`.
`embeddingCoefficientRestriction_evaluation_points` uses composition of actual
point maps and the tensor coefficient identity.
`embeddingIntermediatePoint_evaluation` combines these two identities.
`evaluationComponent_intermediatePoint` is proved directly by the underlying
pullback projections, while `evaluation_intermediatePoint` uses the published
scalar-evaluation point formula.

Thus `evaluationComponent_embeddingEvaluationPoints` states that the actual
pullback component of scalar evaluation, on every affine test point, is exactly
the original tensor point followed by embedding evaluation. Finally,
`embeddingProductIsoOfBijective_component_points` identifies it with the
original coordinate of the published embedding-product isomorphism. All
original maps, scalar actions and point equivalences are retained. This module
establishes point equalities; the equality of group-scheme coordinate morphisms,
canonical Galois compatibility and the structural Weil-restriction theorem are
subsequent obligations.
