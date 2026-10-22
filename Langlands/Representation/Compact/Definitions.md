# Compact-subgroup averaging

Let `G` be a topological group, `V` a complex vector space with no assigned
topology, and `rho` a smooth algebraic representation. For an open subgroup `K`
whose underlying set is compact, `averageMap rho h_rho K h_K` is the complex
linear endomorphism

$$v \longmapsto |K v|^{-1}\sum_{w\in K v}w.$$

Every orbit is finite: a fixing open subgroup for `v`, intersected with `K`,
is open inside `K` and contained in its stabilizer. That stabilizer is open.
Mathlib's compact/discrete quotient theorem makes its coset set finite, and
the orbit-stabilizer equivalence transfers finiteness to the orbit.
Thus this sum is the normalized coset formula for the stabilizer in `K`.
Linearity follows by using the orbit of a pair for addition and by applying the
finite-orbit naturality lemma to scalar multiplication. All nonzero natural
cardinalities are invertible in the explicitly chosen field `Complex`.

`fixedVectorMap` restricts a Mathlib intertwiner to the existing project fixed
submodules. Its definition uses only equivariance. No smoothness transfer theorem
from Worker 0 is asserted or reproved here.

## Original source and scope

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II: *Smooth representations*, revision June 16, 2019, Section 1,
page 3 (normalized compact-subgroup projection), page 4 (finite-coset formula in
the proof of Proposition II.1.2 and the fixed-vector exactness clause of II.1.3).
The actual file is
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
Literature ID: `casselman-2019-smooth-representations`; content SHA256:
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.

The implementation takes complex coefficients and a topological group with a
specified compact open subgroup. Local profiniteness, countability, and finite
dimension are unnecessary for this construction. These are explicit changes
from the chapter's ambient hypotheses, justified by the finite-orbit argument.
There is no Bochner integral and no claim over arbitrary coefficient rings.

## Mathlib audit

At Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`:

- `RepresentationTheory/Invariants.lean` supplies `Representation.invariants`,
  `GroupAlgebra.average`, `Representation.averageMap`, `averageMap_invariant`,
  `averageMap_id`, and `isProj_averageMap`. Its averaging API requires
  `Fintype G` and `Invertible (Fintype.card G : k)`. It does not directly average
  an infinite compact group acting with finite vector orbits.
- `Topology/Algebra/OpenSubgroup.lean` supplies `Subgroup.isOpen_mono`,
  `subgroupOf_isOpen`, and `quotient_finite_of_isOpen`. The last result applies
  to open, not necessarily normal, subgroups of compact groups.
- `GroupTheory/GroupAction/Quotient.lean` supplies
  `MulAction.orbitEquivQuotientStabilizer`. No new finite-index topological
  theorem is needed.

## Exact project dependencies

The smoothness and fixed-vector definitions are the published definition artifact
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1, effective snapshot
`092f2dc612370a1612d3c08d1e60ff18add554e831ee02c7041342ac9dff16c0`.
The local source hashes were checked against its effective record.
`FiniteMean` is the accompanying internal algebraic implementation.
Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 and the Mathlib commit above.

The projection, fixed-vector identity, naturality, and surjectivity properties
will be explicit proposition targets and separate checked proofs. This document
does not identify successful compilation with independent acceptance.
