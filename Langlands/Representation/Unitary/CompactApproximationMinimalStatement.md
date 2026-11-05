# Minimal closed subrepresentations from compact approximations

Worker 116 states `Langlands.Analysis.CompactApproximationMinimalStatement`.
The group G and complete complex inner-product space E have independent
universes. The actual homomorphism π sends G to the bounded complex-linear
endomorphisms of E and preserves the inner product. Invertibility of every
π(g) follows from the group homomorphism laws. No topology on G or continuity
in its group variable is required for this internal operator statement.

The sequence T consists of actual compact symmetric bounded endomorphisms,
and T(n)x tends in norm to x for every x. Each T(n) must preserve every
closed π-invariant complex submodule S. This is stronger than preserving
only the supplied W, and is essential for the minimality argument. The
hypothesis holds for integrated operators once their preservation of closed
subrepresentations has been established; that analytic construction is not
part of this statement. No commutation of T(n) with π(g), or between distinct
T(n), is assumed.

For every supplied nonzero closed π-invariant W, the conclusion gives an
actual complex submodule P of E, contained in W, nonzero, closed and
π-invariant. Every closed π-invariant Q contained in P is either zero or P.
This is a literal minimal-subspace clause. It introduces no new
irreducibility predicate; it expresses the invariant-subspace condition
used by the Library's `Langlands.Archimedean.IsTopologicallyIrreducible`
on the restricted nonzero representation.

The provenance is an internal extraction of the first paragraph in the
proof of Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Lemma 9.3.1, printed p.247, one-based PDF p.259, registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The original page was read directly. The preceding printed p.246 supplies
the symmetric compact approximations and strong convergence arising from
a Dirac sequence. The complete five-page author errata, registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was read and contains no entry for Lemma 9.3.1.

The derivation starts with a nonzero finite-dimensional ambient eigenspace
intersection in W. Among the nonzero intersections of that eigenspace with
closed invariant subspaces of W, choose one of least dimension. A nonzero
vector x in it generates an actual closed invariant subspace P. For a
closed invariant Q contained in P, the orthogonal projection of x to Q is
still in the eigenspace: symmetry and preservation of Q make its projection
commute with the chosen approximating operator. If the projection is
nonzero, least dimension forces the entire chosen intersection into Q,
hence x belongs to Q and cyclicity gives P = Q. If the projection is zero,
x belongs to Q's invariant orthogonal complement. Cyclicity then puts P
there, so Q contained in P must be zero. This supplies the complementary
case left implicit in the printed argument. It is a derivation rationale;
the statement module contains no theorem proof.

No Dirac sequence, integrated representation, adelic quotient, automorphic
Hilbert space, maximal orthogonal family or Hilbert direct-sum decomposition
is constructed. Finite representation multiplicities and the automorphic
applications remain subsequent obligations.
