# A shrinking sequence of continuous Hermitian weights

Worker 116 formulates the internal proposition
`Langlands.Analysis.HermitianWeightSequenceStatement`.
Let G be an actual locally compact Hausdorff topological group with its
Borel measurable space. Assume that the neighborhood filter at its
identity is countably generated. This is a countable local base at the
identity; the proposition does not require a chosen metric or a countable
base for the whole space. Let μ be a measure finite on compact sets and
positive on every nonempty open set, and let d : G →* ℝ≥0 be a continuous
multiplicative homomorphism.

The target asserts existence of one sequence f : ℕ → G → ℝ such that,
for every n:

- f n is continuous and has compact topological support;
- f n is nonnegative everywhere and integrable with respect to μ;
- its real Bochner integral is one;
- f n g = d(g) f n (g⁻¹) for every g.

For every identity neighborhood U, there is an index after which the
topological support of every f n lies in U. The index may depend on U.
Here topological support is the closure of the set where the function
is nonzero. Thus the conclusion also implies eventual containment of
the ordinary supports, as required by
`Langlands.Analysis.IntegratedIsometricApproximationStatement`.
It asserts no nesting of the supports themselves.

The internal route starts with
`Langlands.Analysis.HermitianNeighborhoodWeightStatement`.
A countably generated identity-neighborhood filter has a decreasing
basis V n indexed by natural numbers. Choose a normalized continuous
Hermitian weight supported in each V n by the individual-neighborhood
construction. For any U in the neighborhood filter, some V N lies
inside U. Decreasingness gives support(f n) ⊆ V n ⊆ V N ⊆ U for every
n ≥ N. The sequence is obtained by classical choice. The measure need
not be invariant and is independent of d. Strict positivity of d follows
from d(g)d(g⁻¹) = 1, with no further hypothesis.

This is an internal continuous analogue of the Dirac sequence in
Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
section 9.3, printed p.246, one-based PDF p.258. The original source,
registered as `getz-hahn-2024-automorphic-representations`, has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The original paragraph and Lemma 9.3.1 on printed p.247/PDF p.259
were read directly for this formulation. The complete five-page October
2026 author errata, `getz-hahn-2024-errata-2026-10`, has SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
Its Chapter 9 corrections concern sections 9.2 and 9.5; none changes the
Dirac-sequence paragraph.

The source uses smooth compactly supported functions on the actual
adelic group modulo the split center, right Haar measure, and
d = δ_G⁻¹ in its modular convention. It states eventual support
containment for relatively compact open identity neighborhoods.
The internal target asserts the continuous version on the stated
general group, with an explicit local countability hypothesis, and
asserts containment for every identity neighborhood. Local compactness
allows this stronger support formulation. It does not construct a smooth
Dirac sequence, identify the Haar modular character, prove continuity of
that concrete character, or prove μ.inv = μ.withDensity d.

This file defines a Prop-valued target and contains no proof. A separate
exact published-target proof child is required. The intended integrated
operator application also needs its actual measurable continuous
representation, the inversion-density measure identity for symmetry,
and compactness. Smooth automorphic realization, the split-center
quotient and comparison with existing algebraic Hecke operators remain
separate obligations.
