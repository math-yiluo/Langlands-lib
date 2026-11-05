# The actual equivariant Hilbert sum from compact approximations

Worker 116 states
`Langlands.Analysis.CompactApproximationHilbertSumStatement`.
The group and complete complex inner-product space have independent
universes. The actual homomorphism π into bounded complex-linear
endomorphisms preserves the inner product. No topology or continuity in
the group variable is used.

The sequence consists of actual compact symmetric bounded operators,
converges strongly to the identity, and preserves every closed invariant
complex submodule. Preservation is required for all such submodules,
as in the preceding minimality and orthogonal-family targets. Commutation
of these operators with one another or with the group is not assumed.

For each actual closed invariant W, the conclusion supplies a set A of
actual nonzero minimal closed invariant submodules contained in W.
Minimality is literal: every closed invariant submodule contained in a
member is zero or the whole member. Distinct members are orthogonal.
The external Hilbert sum is Mathlib's actual `lp` of these subspaces with
exponent 2. Its elements are square-summable families of vectors, using
the inherited Hilbert norms. The conclusion gives a complex-linear
isometric equivalence U from this sum onto W.

U is the canonical summation map: each square-summable family has the
unconditional sum of its inclusions into E equal to the inclusion of
U applied to that family. Each single-supported vector maps to its
original vector. These properties identify the equivalence with the
original subspaces and imply their finite sums are dense in W.
The conclusion also supplies an actual homomorphism ρ into bounded
complex-linear endomorphisms of the external sum. Its action on every
coordinate is the original π action on that subspace. U intertwines ρ
and π, and ρ preserves the actual Hilbert inner product.

There is no separability or countability assumption, no prescribed list
of irreducible isomorphism classes, and no finite-multiplicity assertion.
W may be zero, with the empty family and zero Hilbert sum. The summand
index is a subtype of the type of submodules of E, without quantifying
over representations in a larger unspecified universe.

This is an internal extraction and completion of the direct-sum step in
Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Lemma 9.3.1, printed p.247, one-based PDF p.259. The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The original page was read directly. The complete five-page errata,
registered as `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was read and contains no entry for Lemma 9.3.1.

The internal route first uses the preceding orthogonal-family target.
Mathlib's orthogonal-family summation isometry has range exactly the
closed algebraic sum of the complete summands, hence exactly W.
Restricting its codomain gives U. Transport the restricted original
action through U to obtain the homomorphism ρ. For a given group element,
applying π to every coordinate preserves square summability because π
preserves norms. Bounded linear maps preserve convergent sums, so the
canonical summation formula identifies that coordinate action with the
transported action. Inner-product preservation follows through U.

The statement does not construct a Dirac sequence, an integrated action,
an adelic quotient or an automorphic Hilbert space. The final paragraph
of the source's proof, concerning multiplicities, is a separate
obligation: arbitrary equivariant identifications of equivalent
subrepresentations must also respect the particular integrated
operators used in that argument. Preservation of invariant subspaces
alone is not documented here as a substitute for that compatibility.
This file defines a proposition; its exact proof requires a separate
published-target child.
