# Strong approximation by actual integrated isometric actions

Worker 116 states
`Langlands.Analysis.IntegratedIsometricApproximationStatement`.
Let G be an actual group with a topology and measurable space, E a
complete complex normed space, μ any measure on G, and π an actual
homomorphism into bounded complex-linear endomorphisms. Assume pointwise
norm preservation and AE strong measurability of each orbit, as required
by the actual `integratedIsometricAction` constructor. Also assume that
each orbit map g ↦ π(g)x is continuous at the identity. Group and space
universes are independent.

For an actual sequence f_n:G→ℝ, assume each f_n is integrable,
pointwise nonnegative, and has integral one. For every neighborhood U
of the identity, its actual nonzero support is eventually contained in U.
Then the actual bounded operators

T_n x = ∫ g, (f_n(g):ℂ) • π(g)x dμ(g)

converge to x in norm for every x:E. The constructor's complex-weight
integrability proof is obtained from the given real integrability by
`Integrable.ofReal`. The conclusion is genuine strong convergence of
these constructed operators, with no assumed approximation conclusion.
It does not assert convergence in operator norm.

This is an internal Banach-space Bochner formulation of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Definition 3.4.1
and Corollary 3.4.2, printed p.86, one-based PDF p.102, and the strong
convergence part of the Dirac-sequence discussion in section 9.3,
printed p.246, one-based PDF p.258. The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The source uses nonnegative continuous compactly supported weights with
right-Haar integral one and shrinking supports, and its representation
acts on a locally convex quasi-complete space using Pettis integration.
The present complete normed-space Bochner result instead keeps the exact
integrability and orbit measurability assumptions it needs. It assumes
support shrinkage for all identity neighborhoods. In the source's locally
compact Hausdorff group setting, relatively compact open neighborhoods
form a local basis, so the source condition supplies this hypothesis.
The implementation does not assert a formal comparison with a separate
Pettis construction.

The proof route is the elementary integral estimate. Normalization gives
x = ∫ f_n(g) • x. Subtracting from T_n x expresses the error as the
integral of f_n(g) • (π(g)x − x). Continuity at the identity bounds the
orbit difference by ε/2 on one neighborhood. Eventual support containment
and nonnegativity bound the integrand's norm by f_n(g)ε/2 everywhere.
The scalar integral is ε/2, so the vector error is eventually less than ε.
No Haar invariance, group-topology compatibility, finite measure,
separability or operator-valued measurability is used in this argument;
arbitrary measures and the displayed orbit hypotheses suffice.

The complete October 2026 author errata, registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has no correction to section 3.4 or the section 9.3 Dirac-sequence
discussion. The original passages and complete errata were read directly.

This file defines the proposition only. A separate exact published-target
child must prove it. Existence of such normalized weights, continuous
compact support or smoothness of them, modular inversion symmetry,
self-adjointness, compactness and the concrete automorphic Hilbert
realization remain separate obligations. The statement alone does not
establish the compact-approximation hypotheses for an actual automorphic
representation or any spectral decomposition.
