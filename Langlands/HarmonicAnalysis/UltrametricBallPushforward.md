# Haar transport on an ultrametric ball

`map_closedBall_add_perturbation`: let `X` be a proper ultrametric normed
additive group with an additive Haar measure `μ`, let `a ∈ X` and `r ≥ 0`, and let
`u : X → X` be continuous with Lipschitz constant strictly below one on the closed
ball `B(a, r)`. Then `x ↦ x + u(x)` sends `μ` restricted to `B(a, r)` to `μ`
restricted to `B(a + u(a), r)`.

On the ball the map preserves distances: `‖u(x) − u(y)‖ < ‖x − y‖` for `x ≠ y`,
so the strong triangle inequality gives `‖(x + u x) − (y + u y)‖ = ‖x − y‖`. For
every `b` in `B(a + u(a), r)`, the map `x ↦ b − u(x)` is a contraction of the
complete ball `B(a, r)` into itself, and its Banach fixed point is a preimage of
`b`. So the image of `B(a, r)` is `B(a + u(a), r)`.

To compare the two finite measures, test on closed balls of positive radius,
which form a topological basis and a π-system generating the Borel σ-algebra.
A test ball disjoint from the image ball has measure zero for both. Otherwise
choose a point in the intersection and its preimage `b`. By the ultrametric
recentring identities and distance preservation, the preimage of the test ball
of radius `t` within `B(a, r)` is the ball about `b` of radius `min t r`, and the
intersection of the test ball with the image is the ball about `b + u(b)` of the
same radius. Additive Haar gives these two balls equal mass by translation
invariance.

This lemma is used by `compactSubmersionPushforward` in
`Langlands.HarmonicAnalysis.CompactSubmersionPushforward`.
