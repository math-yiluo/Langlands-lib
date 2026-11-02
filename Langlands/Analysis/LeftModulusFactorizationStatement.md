# Contractive factorization through the positive left modulus

`Langlands.Analysis.OperatorIdeals.LeftModulusFactorizationStatement`
asserts that every bounded complex-linear endomorphism A of a complete
complex inner-product space E has a bounded endomorphism U such that
`‖U‖ ≤ 1` and `A = (leftModulus A).comp U`. The space has an arbitrary
universe. No separability, finite-dimensionality, injectivity or
closed-range premise is imposed.

The existing left modulus is `L = CFC.sqrt (A * star A)`, so `L² = A A*`
and L is positive. Composition order is essential: the conclusion is
`A x = L (U x)`. This uses the left modulus convention in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Definition 9.1.1
and equation (9.3), printed p.240, one-based PDF p.252. The registered
source is `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
That passage and the p.241 independence assertion and Exercise 9.1 on
p.267 were read directly. The complete five-page October 2026 author
errata, source `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was read and does not change those passages.

This factorization is an internal analytic prerequisite for the source's
trace construction, not a theorem attributed to those source passages.
Its derivation uses the identity `‖A* x‖ = ‖L x‖`. Define a linear map on
the range of L by `L x ↦ A* x`. The norm identity makes this map
well-defined and contractive. Extend it continuously to the closure of
that range and compose with the orthogonal projection onto the closure.
The resulting contraction V satisfies `A* = V L`. Taking adjoints and
using self-adjointness of L gives the conclusion with `U = V*`.
Continuous extension and orthogonal projection are the actual
constructions from the pinned Mathlib, rather than assumed
factorization data.

The proposition does not assert that U is a partial isometry, its
uniqueness or a specified initial or final subspace. It constructs no
canonical polar decomposition. It does not assert trace-diagonal
summability or basis independence, Hilbert–Schmidt product trace class,
or any automorphic operator theorem. Its proof is a separate exact-target
obligation after this statement is published.
