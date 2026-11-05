# The bounded operator of an integrable isometric action

Worker 116 constructs `Langlands.Analysis.integratedIsometricAction`.
Let G be an actual group with a measurable space, E a complete complex
normed vector space, μ any measure on G, and π an actual group
homomorphism into bounded complex-linear endomorphisms of E. Assume that
every π(g) preserves the norm and that each orbit map g ↦ π(g)x is
μ-almost everywhere strongly measurable. For an actual function f:G→ℂ
with `Integrable f μ`, the constructed bounded operator is literally

π(f)x = ∫ g, f(g) • π(g)x dμ(g).

The group and vector space have independent universes. There is no
operator-norm measurability assumption on g ↦ π(g), which would exclude
many strongly continuous unitary representations. No topology on G,
Haar property of μ, finite measure or separability of E is required.
The orbit measurability premise is explicit and must be established in
an application; continuity alone is not silently substituted for it.

`isometricActionIntegrand_integrable` proves actual Bochner integrability
by the pointwise identity ‖f(g) • π(g)x‖ = ‖f(g)‖ ‖x‖ and the integrable
scalar majorant. `integratedIsometricActionLinear` uses that integrability
for additivity and the Bochner scalar identity for complex linearity.
`integratedIsometricActionLinear_bound` bounds the vector norm by
(∫ ‖f(g)‖ dμ(g)) ‖x‖. The final construction uses `LinearMap.mkContinuous`
with this bound. Its application formula is definitional, and
`integratedIsometricAction_norm_le` gives the same scalar L1 bound on
its operator norm. These are the construction's intrinsic verification
lemmas, not a supplied boundedness field or a claimed spectral theorem.

This is an internal Banach-space Bochner implementation of the integrated
action in Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), section 3.4, printed pp.85–86, one-based PDF pp.101–102. The
registered source is `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The original formula uses f(g)π(g)x and right Haar measure; our formula
has the same action convention and permits any measure because no
translation or convolution identity is asserted here. The source defines
its vector-valued integral by Gelfand–Pettis integration. We implement the
Bochner integral under explicit strong measurability and norm integrability
hypotheses, rather than assert equality with a separately constructed
Pettis object. The source observes boundedness in the unitary case and
extends it to scalar L1 functions. Norm preservation suffices for the
present construction, so no inner product is required. Hilbert unitary
actions meet the norm condition, but their concrete measurable realization
remains an application obligation.

The complete October 2026 author errata, registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has no section 3.4 correction. The original construction pages and the
complete errata were read directly.

This construction provides neither a convolution algebra homomorphism,
Dirac sequence, self-adjointness, compactness, strong approximation,
closed-invariant-subspace preservation theorem, nor intertwiner naturality
theorem. The latter two are separate exact proposition and proof units.
It constructs no automorphic quotient, Haar measure or spectral
realization. The existing algebraic smooth Hecke integrated action in
`Langlands.Representation.Hecke.IntegratedAction` uses finite-sum
integration without a topology on its carrier; identifying that action
with this Bochner construction on a concrete common realization is a
separate comparison obligation.
