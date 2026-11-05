# A nonzero eigenspace from compact approximations

Worker 116 states `Langlands.Analysis.CompactApproximationEigenspaceStatement`
for a complete complex inner-product space E in an arbitrary universe. The
sequence T consists of actual bounded complex-linear endomorphisms. Every
T(n) is compact and symmetric, and T(n)x converges in norm to x for every
vector x. A supplied complex submodule W is nonzero, closed in E, and
preserved by every T(n).

The conclusion gives an index n and a nonzero complex number μ for which
the actual ambient intersection
`W ⊓ Module.End.eigenspace (T n).toLinearMap μ` is nonzero and
finite-dimensional over ℂ. The intersection need not be invariant under
any additional group action. Symmetry uses Mathlib's complex inner-product
convention, conjugate-linear in the first argument. No separability,
finite-dimensional ambient space, commuting family, or group action is
assumed.

This is an internal functional-analytic extraction of the first step in
the proof of Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Lemma 9.3.1, printed pp.246–247 (one-based PDF pp.258–259),
registered source `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
Those original pages were read directly. In the source, T(n) is the
integrated operator of a Dirac sequence and W is a nonzero closed
subrepresentation. The target retains precisely the operator properties
needed to find its nonzero finite-dimensional eigenspace, allowing any
preserved closed submodule. The complete five-page October 2026 author
errata, registered as `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was read and has no entry for Lemma 9.3.1.

The intended derivation restricts T(n) to the complete submodule W.
Strong convergence prevents every restriction from being zero. The compact
symmetric spectral theorem then supplies a nonzero eigenvalue of one
restriction. Inclusion into E gives the nonzero intersection, and the
ambient compact operator's nonzero eigenspace supplies finite dimension.
This paragraph describes the derivation of the statement; this module
contains no theorem proof.

The statement constructs no Dirac sequence, integrated representation,
adelic quotient or automorphic Hilbert space. It does not assert the
existence of an irreducible subrepresentation, a Hilbert direct-sum
decomposition, finite representation multiplicities, or an automorphic
spectral theorem. Those are subsequent obligations of the program.
