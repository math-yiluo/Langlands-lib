# Finite unitary multiplicity from compatible compact approximations

Worker 116 states
`Langlands.Analysis.CompactApproximationMultiplicityStatement`.
The group and complete complex inner-product space have independent
universes. The actual homomorphism π into bounded complex-linear
endomorphisms preserves the inner product. The sequence T consists of
actual compact symmetric bounded operators, converges strongly to the
identity, and preserves every closed π-invariant complex submodule.

There is an additional, explicit compatibility premise. For every actual
closed invariant submodule P, every actual submodule Q and every
complex-linear isometric equivalence U from P onto Q, if U intertwines the
restricted group action, it also intertwines every T(n). The equations are
equalities of the actual vectors in E. The action and T(n) on P use their
actual invariant restrictions, with the displayed membership proofs.
This premise is the naturality property of integrated representation
operators. In an application it must be proved from the actual integral
formula and boundedness of U. Mere preservation of invariant subspaces
does not establish it.

For any actual set A of pairwise orthogonal nonzero closed invariant
submodules, and each member P, the conclusion says that the set of members
Q admitting an actual group-intertwining complex-linear isometric
equivalence P ≃ Q is finite. Thus the asserted finiteness is the number of
unitarily equivalent copies in the supplied orthogonal family. A need
not span E, and the members need not be irreducible. In particular, when
A is the minimal family in the preceding Hilbert-sum target, this gives
finite multiplicity for each unitary equivalence class occurring in that
decomposition. This statement supplies no Hilbert decomposition itself,
no numerical value for a multiplicity, and no comparison with algebraic
Hom-space dimensions.

This is an internal extraction of the final paragraph of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Lemma 9.3.1,
printed p.247, one-based PDF p.259. The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The original page and its operator setup on printed p.246 were read
directly. The complete October 2026 author errata is registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`;
it has no entry for Lemma 9.3.1.

The source selects a nonzero eigenvalue of one integrated operator on an
irreducible representation and bounds its multiplicity using the finite
dimension of the corresponding ambient eigenspace. The internal version
uses the same argument for any nonzero closed invariant P, without
requiring its irreducibility. The preceding eigenspace target gives
some n, a nonzero eigenvalue λ, and a nonzero vector x in P with
T(n)x = λx. For each equivalent member Q, choose its witnessing U.
The explicit compatibility premise makes Ux an ambient λ-eigenvector.
These vectors are nonzero and mutually orthogonal because their
submodules are orthogonal. They are therefore linearly independent in
the finite-dimensional λ-eigenspace of the actual compact operator
T(n). Their index set is finite. This retains exactly the integrated
compatibility used implicitly when the source identifies the operators
on equivalent representations.

No group topology, Haar measure, integrated operator, Dirac sequence or
automorphic Hilbert space is constructed here. Their existence,
strong approximation and the displayed compatibility remain genuine
application obligations. The conclusion is a finite-multiplicity
criterion with that premise, and does not establish an automorphic
spectral theorem. This file defines a proposition; its Lean proof
requires a separate child after publication of the exact target.
