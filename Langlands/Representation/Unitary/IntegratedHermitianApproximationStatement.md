# Continuous Hermitian integrated approximation

Worker 116 formulates the internal proposition
`Langlands.Analysis.IntegratedHermitianApproximationStatement`.
It assembles the preceding continuous scalar-weight, actual Bochner
operator, symmetry, approximation and naturality interfaces.

Let G be an actual locally compact Hausdorff topological group with its
Borel measurable space and a countably generated neighborhood filter at
the identity. Let μ be a measure finite on compact sets and positive on
nonempty open sets. Let d : G →* ℝ≥0 be continuous. Assume the actual
measure equality

μ.inv = μ.withDensity (g ↦ d(g)).

Let E be a complete complex inner product space and let
π : G →* (E →L[ℂ] E) preserve the complex inner product. Every orbit is
assumed AE strongly measurable for μ and continuous at the identity.
Group and Hilbert-space universes are independent. No separability
hypothesis is imposed.

There exist actual real functions f n and proofs of their integrability
such that each f n is continuous, compactly supported, nonnegative, has
integral one and satisfies f n(g) = d(g) f n(g⁻¹) everywhere. Their
topological supports eventually lie in every identity neighborhood.
For the actual constructed operators

A n x = ∫ g, (f n(g) : ℂ) • π(g)x ∂μ,

the conclusion asserts symmetry, operator norm at most one and strong
convergence A n x → x for every x. The operators in this conclusion
are exactly `integratedIsometricAction` for the displayed weights,
with norm preservation derived from the inner product identity.
They are not an independent family supplied as a hypothesis.

Every closed invariant complex submodule P is preserved by all A n.
Every actual group-intertwining complex-linear isometric equivalence
U : P ≃ₗᵢ[ℂ] Q also intertwines all A n, with values compared in the
ambient E. The conclusion provides the preservation proofs used to form
the submodule elements in this equation. No separate closedness,
completeness or invariance hypothesis on Q is required.

The internal route chooses f using `HermitianWeightSequenceStatement`.
Real integrability gives complex integrability. The pointwise real
Hermitian equation becomes the complex Hermitian equation because
complex conjugation fixes real values. `IntegratedUnitarySymmetryStatement`
applies using continuity, hence measurability, of d and the actual
inversion-density equality. The constructor's L1 norm bound equals one
by nonnegativity and normalization. Ordinary support lies inside
topological support, so `IntegratedIsometricApproximationStatement`
gives strong convergence. Applying
`IntegratedIsometricNaturalityStatement` to each weight supplies the
preservation and intertwiner conclusions.

The motivating original is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), section 9.3, printed pp.246–247, one-based PDF
pp.258–259. The registered source
`getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
Those original pages were read directly for this assembly. The paragraph
preceding Lemma 9.3.1 combines normalized shrinking Hermitian weights,
strong approximation and self-adjointness; the proof of that lemma also
uses invariant-subspace preservation and intertwiner compatibility.
The norm bound here is an internal consequence of the actual Bochner
construction and nonnegative normalization.

The original uses smooth compactly supported weights on the actual
adelic group modulo the split center and right Haar measure. Its
modular convention gives d = δ_G⁻¹. This target uses continuous weights
on the stated general group, explicitly assumes local countability and
the inversion-density equality, and does not identify d with the
modular character of any concrete Haar measure. The complete five-page
October 2026 author errata, registered as
`getz-hahn-2024-errata-2026-10`, has SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
It was read in full; its Chapter 9 corrections concern sections 9.2
and 9.5, and do not change the cited section 9.3 paragraph.

This file defines a Prop-valued target and contains no proof.
A separate exact published-target proof child remains required.
This assembly supplies symmetric contractions and strong approximation
under the displayed measure and action hypotheses. It does not assert
that these operators are compact. Smooth scalar weights, actual Haar
and modular-density constructions, the automorphic Hilbert action,
comparison with algebraic Hecke operators, compactness, and a
spectral-decomposition application remain separate obligations.
