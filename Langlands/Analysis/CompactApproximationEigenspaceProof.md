# Proof of the compact-approximation eigenspace step

Worker 116 proves
`Langlands.Analysis.compactApproximationEigenspace` with theorem type exactly
`Langlands.Analysis.CompactApproximationEigenspaceStatement.{u}`. The complete
complex inner-product space has an arbitrary universe. All hypotheses and
the actual ambient intersection are those of the statement.

Closedness makes the supplied submodule W complete. Choose a nonzero vector
x in W. If every T(n)x were zero, strong convergence would make the constant
zero sequence converge to x. Uniqueness of limits would give x=0. Thus one
T(n) acts nontrivially on W.

The proof forms the actual bounded restriction S of this T(n) to W using
the preservation hypothesis. Evaluation on x shows S is nonzero. Mathlib's
`IsCompactOperator.restrict'` and
`LinearMap.IsSymmetric.restrict_invariant` transfer compactness and
symmetry to S. The contrapositive of
`ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero` gives a
nonzero eigenvalue μ of S.

An eigenvector y in W remains nonzero under the subtype inclusion into E.
Applying that inclusion to its eigenvector equation places y in the actual
ambient μ-eigenspace of T(n), and hence proves the intersection with W is
nonzero. Mathlib's `ContinuousLinearMap.finite_dimensional_eigenspace`
makes the ambient μ-eigenspace finite-dimensional because μ is nonzero.
`Submodule.finiteDimensional_of_le` transfers this to the intersection.
No spectral-basis or countability assumption is introduced.

The source motivation is the first paragraph of the proof of Getz–Hahn
(2024), Lemma 9.3.1, printed pp.246–247 (one-based PDF pp.258–259), in
registered source `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The full October 2026 author errata
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has no entry for that lemma. The implemented proof uses the pinned
Mathlib compact symmetric spectral theorem on the restriction, then
includes one eigenvector into the ambient space. It proves the internal
operator lemma only. The representation-theoretic minimality argument,
orthogonal direct-sum construction, multiplicity bound and automorphic
application are separate subsequent steps.
