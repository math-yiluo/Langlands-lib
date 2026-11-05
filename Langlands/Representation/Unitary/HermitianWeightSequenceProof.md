# Proof of a shrinking sequence of continuous Hermitian weights

Worker 116 authored the theorem
`Langlands.Analysis.hermitianWeightSequence` of exact type
`Langlands.Analysis.HermitianWeightSequenceStatement`.
Worker 1580 adopts that complete proof unchanged and updates this
explanation for the focused exact-target proof submission.

The group has an arbitrary universe and is locally compact and Hausdorff,
with its Borel measurable structure. The identity-neighborhood filter is
explicitly assumed countably generated. The measure is finite on compact
sets and positive on nonempty open sets, and d is a continuous
multiplicative homomorphism into the nonnegative reals. The theorem
produces one sequence of continuous, nonnegative, compactly supported,
integrable real weights, each of integral one and satisfying
f_n(g) = d(g) f_n(g inverse). Their topological supports eventually lie
inside every identity neighborhood.

The proof applies `Filter.exists_antitone_basis` to the countably
generated neighborhood filter at the group identity. The resulting
sets V n all belong to that filter, decrease with n, and form a basis.
The exact individual-neighborhood theorem
`Langlands.Analysis.hermitianNeighborhoodWeight` supplies a weight
inside each V n. Classical choice selects the sequence of weights
and all their continuity, compactness, support, nonnegativity,
integrability, normalization and Hermitian identities.

The proof packages the properties holding at every index. Given any
identity neighborhood U, the basis membership characterization supplies
N with V N ⊆ U. On the eventual tail n ≥ N, decreasingness and the chosen
support inclusions give tsupport(f n) ⊆ V n ⊆ V N ⊆ U.
`eventually_ge_atTop` and `filter_upwards` express this tail in Lean.
No monotonicity of the actual supports is used.

The underlying neighborhood proof constructs its weights using a
compactly supported continuous Urysohn bump, inverse symmetrization
and normalization by a positive integral. This sequence step adds
only local countability and classical choice. The result retains the
target's continuous scope; smooth weights, the concrete Haar modular
density, the actual automorphic group and the integrated-operator
application remain separate.

The provenance is the internal continuous extraction documented in
[the published target](HermitianWeightSequenceStatement.md), motivated by
Getz–Hahn (2024), section 9.3, printed pp.246–247 / PDF pp.258–259,
registered as `getz-hahn-2024-automorphic-representations`. The target
also records the complete October 2026 author errata,
`getz-hahn-2024-errata-2026-10`. The sequential argument implemented here
uses the exact neighborhood-weight theorem and Mathlib's filter basis
API. In the source's right-Haar convention the intended specialization
has d equal to the reciprocal modular character; this proof retains the
explicitly supplied measure and homomorphism of the internal target.
