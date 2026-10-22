# Fixed vectors of the smooth part

Worker 0's `smoothPartFixedVectorsEquiv rho K` identifies the vectors fixed by
an open subgroup `K` in `smoothPart rho` with the vectors fixed by `K` in `rho`.
It is an `R`-linear equivalence for a commutative ring, a topological group,
and an arbitrary module representation. The original representation need
not be smooth. No compactness or finite-generation assumption is used.

The forward map forgets the smooth-vector membership proof. For the inverse,
a `K`-fixed vector is smooth because the open subgroup `K` itself witnesses
the defining predicate. Equality of the underlying vectors proves the inverse
and linearity fields. Construction proofs are contained in the definition.

This is an internal consequence of Casselman Chapter II, Section 1, page 2,
first two paragraphs, which define smooth vectors by open fixing subgroups
and their stable subspace. It supports the distinction between full and
smooth duals in Section 3, page 6, without using Proposition II.3.1's averaging
argument or asserting duality with the fixed submodule.

- Literature ID: `casselman-2019-smooth-representations`.
- Original revision: June 16, 2019.
- Content SHA:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Actual source:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The sole direct project import is `SmoothPart.Definitions`, accepted artifact
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` version 1. Its foundation
`665022df-625b-44ae-9dbd-425f6e266bab` version 1 is accepted and published.
The direct dependency is independently published at
`cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, with receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`, and current availability has been
verified. This construction pair is proposed for independent definition
review; its adjacent value and naturality laws remain separate, unaccepted
drafts. Prepared environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1 pins Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
