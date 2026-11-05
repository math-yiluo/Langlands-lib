# Normalized Hermitian weights in identity neighborhoods

Worker 116 formulates the internal proposition
`Langlands.Analysis.HermitianNeighborhoodWeightStatement`.
Let G be a locally compact Hausdorff topological group, with its Borel
measurable space, and let μ be a Borel measure finite on compact sets and
positive on every nonempty open set. Let d : G →* ℝ≥0 be an actual
continuous multiplicative homomorphism. For every neighborhood U of the
identity, the target asserts existence of a real function f with all of
these properties:

- f is continuous and has compact topological support contained in U;
- f is nonnegative everywhere and is genuinely integrable with respect to μ;
- its actual Bochner integral is one;
- f(g) = d(g) f(g⁻¹) for every g.

A homomorphism from a group to the multiplicative nonnegative reals has
strictly positive values: its value at g times its value at g⁻¹ is one.
In particular d(1) = 1. No independent positivity assumption on d is
needed. The measure is not assumed invariant. No inversion-density
identity is inferred for it from the supplied homomorphism.

This is an internal continuous-weight construction motivated by the
Dirac-sequence paragraph of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), section 9.3, printed p.246, one-based PDF p.258.
The original source is registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The original paragraph and Lemma 9.3.1 on the following page were read
directly for this formulation. The complete five-page October 2026 author
errata, registered as `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was also read. Its Chapter 9 corrections concern sections 9.2 and 9.5;
none changes this Dirac-weight paragraph.

The source uses smooth compactly supported weights, a sequence, right
Haar measure, and d = δ_G⁻¹ in its modular convention. This target supplies
continuous weights in individual neighborhoods. Smoothness, a shrinking
sequence or net, the concrete modular character and its continuity, and
the actual equality μ.inv = μ.withDensity d are separate obligations.
In particular this proposition does not assert a Getz–Hahn smooth Dirac
sequence or an automorphic spectral decomposition. Passing from a weight
in each neighborhood to a sequence requires a countable local base; no
such countability hypothesis is imposed or concluded here.

The internal derivation uses a symmetric open identity neighborhood V
inside U and a continuous compactly supported Urysohn bump φ with
φ(1) = 1, 0 ≤ φ ≤ 1 and topological support in V. Set
ψ(g) = φ(g) + d(g) φ(g⁻¹). The homomorphism inverse identity gives
ψ(g) = d(g) ψ(g⁻¹). This function is continuous, nonnegative, compactly
supported inside U, and ψ(1) = 2. Positivity of μ on nonempty open sets
makes c = ∫ ψ strictly positive; finiteness on compact sets ensures
integrability. Then f = ψ/c has exactly the asserted properties.
The target is a Prop-valued definition; this file supplies no proof.
A separate exact published-target proof child is required.

The independent integrated-unitary symmetry target applies to the complex
coercion of these real weights only after its actual measure identity and
representation hypotheses have been supplied. Compactness of integrated
operators, invariance and intertwining, strong approximation, smooth
realization and comparison with the algebraic Hecke action remain
separate requirements for the cuspidal application.
