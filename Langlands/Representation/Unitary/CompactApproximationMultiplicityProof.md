# Proof of finite unitary multiplicity from compact approximations

Worker 116 proves `Langlands.Analysis.compactApproximationMultiplicity`
with theorem type exactly
`Langlands.Analysis.CompactApproximationMultiplicityStatement.{uG, uE}`.
The actual group and complete complex inner-product space retain independent
universes. The target's operator-intertwining premise is used explicitly.

Apply `Langlands.Analysis.compactApproximationEigenspace` to the chosen
member P of the supplied orthogonal family. Its closedness, nonzero
condition and invariance under the approximations follow from the target's
premises. This supplies an index n, a nonzero scalar μ and a nonzero vector
x in the intersection of P with the ambient μ-eigenspace F of T(n).
Mathlib's `ContinuousLinearMap.finite_dimensional_eigenspace` makes F
finite-dimensional.

Let B be the actual set of members Q admitting a group-intertwining
complex-linear isometric equivalence from P. Choose one witnessing
equivalence U(Q) for each member of B. View x in P. The target's explicit
compatibility premise gives
T(n)(U(Q)x) = U(Q)(T(n)x) = μ U(Q)x.
The second equality uses complex linearity. This places each transported
vector in the same actual ambient eigenspace F. No commutation of T(n)
with the group action or with other approximations is used.

Each transported vector is nonzero because U(Q) is injective and the
inclusion of Q in E is injective. Distinct indices in B have distinct
ambient submodules, so the family's assumed pairwise orthogonality makes
their transported vectors orthogonal. The inherited inner product on F
is the ambient inner product. Mathlib's
`linearIndependent_of_ne_zero_of_inner_eq_zero` therefore gives a
linearly independent family in F indexed by B.
`LinearIndependent.finite` makes that index type finite, and
`Set.toFinite` gives the required finiteness of the actual set B.

The source motivation is the last paragraph of Getz–Hahn (2024),
Lemma 9.3.1, printed p.247 (one-based PDF p.259), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata, registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has no entry for this lemma. The implemented internal extraction proves
finiteness directly from orthogonal transported eigenvectors and does
not require irreducibility or that the family span E.

The proof consumes the exact compatibility assumption in the published
target. For genuine integrated representations, this must still be proved
from the actual integral formula. It does not construct those integrals,
a Dirac sequence, an automorphic realization, or a Hilbert decomposition.
Those application and construction obligations remain separate.
