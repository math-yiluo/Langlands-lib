# Actual right Haar Hermitian approximation

Worker 116 formulates the internal proposition
`Langlands.Analysis.RightHaarHermitianApproximationStatement`.
It specializes `IntegratedHermitianApproximationStatement` to the inverse
of an actual left Haar measure and the intrinsic modular character.

Let G be a locally compact Hausdorff second countable topological group,
in an arbitrary universe, with its Borel measurable space. Let μ be any
actual left Haar measure in Mathlib's `IsHaarMeasure` convention.
Let E be a complete complex inner product space in an independent universe.
Let π be a monoid homomorphism from G to the continuous complex-linear
endomorphisms of E, preserving the inner product, with every orbit
g ↦ π(g)x continuous. The integration measure is the actual inverse
measure μ.inv, which is right invariant. No separability assumption on E
is imposed.

The conclusion supplies a sequence of real functions f n, integrable for
μ.inv, continuous, compactly supported, nonnegative and of integral one.
They satisfy, for every g,

f n(g) = modularCharacter(g⁻¹) f n(g⁻¹).

Their topological supports eventually lie inside every identity
neighborhood. The conclusion concerns the actual constructed continuous
linear operators

A n x = ∫ g, (f n(g) : ℂ) • π(g)x ∂μ.inv.

In Lean these operators are `integratedIsometricAction`, with norm
preservation derived from the inner product identity and AE strong
measurability derived from orbit continuity. They are symmetric contractions
and converge strongly to the identity on every vector. Every closed
π-invariant complex submodule P is preserved by every A n. Every
complex-linear isometric equivalence from P to another submodule Q that
intertwines π also intertwines every A n, with both sides compared in E.
No separate closedness or invariance hypothesis on Q is needed.

This specialization removes the supplied inversion-density equality and
the supplied orbit measurability from the generic assembly target.
`HaarInversionDensityStatement` supplies

μ = μ.inv.withDensity (g ↦ modularCharacter(g⁻¹)).

Inversion is involutive, so this is exactly the density identity needed
for the right measure μ.inv. The reciprocal modular homomorphism is
continuous by `Langlands.Haar.continuous_modularCharacter_of_locallyCompact`
and continuity of inversion. The inverse measure is finite on compact
sets and positive on nonempty open sets. Second countability of G implies
countable generation at the identity and makes continuous orbits strongly
measurable even when E is not separable. These are derived prerequisites,
not additional hypotheses.

The motivating original is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), section 3.2, printed pp.81–82, one-based PDF
pp.97–98, especially (3.8), and section 9.3, printed pp.246–247, PDF
pp.258–259. The registered source
`getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
Those four original pages were read directly before freezing this target.
Mathlib's right-pushforward modular character agrees with GH's δ_G,
and modularCharacter(g⁻¹) is δ_G(g)⁻¹. GH uses right Haar measure and this
reciprocal character in the Hermitian weight equation. GH's term
"Haar measure" also includes right invariance, whereas Mathlib's
`IsHaarMeasure` denotes left Haar measure; this target uses the latter
convention for μ and integrates against μ.inv.

The complete five-page October 2026 author errata, registered as
`getz-hahn-2024-errata-2026-10`, has SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
It was read in full. Its section 3.2 correction concerns quotient-measure
notation, and the Chapter 9 corrections concern sections 9.2 and 9.5;
they leave the cited modular and approximation formulas unchanged.

This is a Prop-valued statement with no proof. Its internal proof route
uses the Haar inversion-density theorem and the generic continuous
Hermitian approximation theorem. Those prerequisites require their own
independent accepted-public proofs before an exact-target proof child
can submit this specialization. The continuous weights here precede GH's
smooth adelic weights. Smoothness, the actual automorphic Hilbert action,
comparison with algebraic Hecke operators, compactness and spectral
decomposition remain separate obligations.
