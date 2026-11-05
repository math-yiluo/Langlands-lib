# Symmetry of the actual integrated unitary action

Worker 116 formulates the internal proposition
`Langlands.Analysis.IntegratedUnitarySymmetryStatement`. Let G be a group
with a measurable space and measurable inversion, E a complete complex
inner product space, μ a measure on G, and π an actual group homomorphism
into bounded complex-linear endomorphisms of E. Assume that every π(g)
preserves the inner product and that each orbit is AE strongly measurable
with respect to μ. Norm preservation, needed by the imported
`integratedIsometricAction`, is derived from inner product preservation by
`LinearMap.norm_map_iff_inner_map_map`.

Let d : G → ℝ≥0 be measurable. The measure hypothesis is the actual equality

μ.inv = μ.withDensity (g ↦ d(g)).

Here `μ.inv` is the pushforward of μ by inversion, and the density is coerced
to the extended nonnegative reals. For every actual integrable complex
weight f satisfying, μ-almost everywhere,

f(g) = d(g) conjugate(f(g⁻¹)),

the constructed bounded operator T = integratedIsometricAction(μ,π,f)
is symmetric:

⟪T x, y⟫ = ⟪x, T y⟫ for all x,y in E.

Mathlib's complex inner product is conjugate linear in its first
argument. Its `ContinuousLinearMap.IsSymmetric` expresses exactly this
displayed identity; for an everywhere defined bounded operator on this
Hilbert space it is the usual self-adjointness condition. No operator
symmetry or equality of matrix-coefficient integrals is assumed.
The group and space universes are independent.

The motivating original is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), section 3.2, printed pp.81–82, one-based PDF
pp.97–98; section 3.4, printed pp.85–86, PDF pp.101–102; and the
Dirac-sequence discussion in section 9.3, printed p.246, PDF p.258.
The registered source is `getz-hahn-2024-automorphic-representations`,
SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
Those original passages were read directly while preparing this target.

The source uses right Haar measure dr, the positive-action integral
∫ f(g)π(g)x dr(g), and the modular convention dr(hg) = δ_G(h)dr(g).
It sets dl(g) = dr(g⁻¹) and records dr(g) = δ_G(g)dl(g) in (3.8).
Thus the inversion density relative to dr is δ_G⁻¹. Its nonnegative
real Dirac weights obey f(g) = f(g⁻¹)δ_G⁻¹(g), precisely the real-weight
specialization of this target's Hermitian relation. Unlike a condition
f(g) = f(g⁻¹), the target retains the modular correction.

The complete five-page October 2026 author errata was also read. It is
registered as `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
That edition has no correction to (3.8), section 3.4 or the section 9.3
Dirac-sequence symmetry assertion. Its section 3.2 correction concerns
quotient-measure notation after Theorem 3.2.3, outside this target.

The internal generalization isolates precisely the measure and
representation identities used by the argument. It permits any measure
with the displayed inversion density, complex Hermitian weights and
arbitrary Hilbert dimension. It assumes no group topology, Haar
invariance, nonnegativity of f, normalization, support condition,
separability, compactness or strong approximation.

For the derivation, first move the weighted Bochner integral through
the inner product, using its proved integrability and complex
conjugation. Unitarity and the group inverse law give
⟪π(g)x,y⟫ = ⟪x,π(g⁻¹)y⟫. Apply inversion as a measurable equivalence
and then the actual with-density formula. The scalar factor becomes
d(g) conjugate(f(g⁻¹)) = f(g) almost everywhere. Commuting the
remaining integral with the inner product gives the claimed identity.
No completeness or orbit measurability with respect to μ.inv is needed,
since no second vector integral operator for that measure is constructed.

This file is a proposition target, not its proof. A separate exact
published-target proof child remains required. Constructing a Haar
measure, identifying its actual inversion density with the source's
modular character on a concrete group, constructing Dirac weights,
proving compactness, comparing with Pettis or algebraic Hecke integrals,
and realizing the automorphic Hilbert action remain separate
obligations. This assertion supplies no spectral decomposition.
