# Dense orthogonal families of minimal closed subrepresentations

Worker 116 states
`Langlands.Analysis.CompactApproximationOrthogonalStatement`.
The group G and complete complex inner-product space E have independent
universes. The actual homomorphism π into bounded complex-linear
endomorphisms preserves the inner product. No topology on G or continuity
in its group variable is used in this internal operator statement.

The actual operators T(n) are compact and symmetric, converge strongly
to the identity, and preserve every closed π-invariant complex submodule.
The last hypothesis is the genuine integrated-operator input retained
from the preceding minimality target; preserving only W would not supply
that argument. The operators need not commute with π or with one another.

For every closed invariant W, including W = 0, the conclusion supplies
an actual set A of actual complex submodules of E. Every member is
contained in W, nonzero, closed, invariant and minimal: each closed
invariant submodule contained in it is either zero or the whole member.
Distinct members are orthogonal in the actual inner product.
`sSup A` is their algebraic sum, and its topological closure is W.
Thus their finite sums are dense in W. There is no separability or
countability premise, and the empty family is allowed when W is zero.
The family is indexed by a set of submodules of E, without increasing
the universe to accommodate a collection of arbitrary representations.

This is an internal extraction of the second paragraph in the proof of
Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Lemma 9.3.1, printed p.247, one-based PDF p.259. The source is registered
as `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`;
the original page was read directly. The full five-page author errata,
registered as `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was read and contains no entry for Lemma 9.3.1.

The derivation uses the preceding actual minimal-subspace result.
Order sets of pairwise orthogonal minimal closed invariant subspaces by
inclusion. A chain has its union as an upper bound, since any two
members occur together in one chain element. Zorn's lemma gives a
maximal family. Its closed algebraic sum K is contained in W and is
invariant, because the operators π(g) are bounded. Unitarity makes
K's orthogonal complement invariant. If K is proper in W, the relative
orthogonal complement K-perp intersected with W is a nonzero closed
invariant subspace, by orthogonal projection onto K. The preceding
minimality result supplies a nonzero minimal subspace in that complement.
It is orthogonal to every member of the family and cannot already
belong to it, contradicting maximality.

This route makes the chain-upper-bound argument explicit by ordering
orthogonal families rather than already decomposed subrepresentations.
The statement asserts existence and density; it does not construct an
isometric equivalence from an actual Hilbert direct sum, or prove finite
representation multiplicities. No Dirac sequence, integrated action,
adelic quotient or automorphic Hilbert space is constructed here.
