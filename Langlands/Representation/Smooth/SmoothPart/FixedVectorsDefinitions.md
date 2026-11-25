# Fixed vectors of the smooth part

`smoothPartFixedVectorsEquiv rho K` identifies the vectors fixed by
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

The sole direct project import is `SmoothPart.Definitions`. Its foundation
is `Langlands.Representation.Smooth.Definitions`.
Preparation environment: Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

The construction covers the linear equivalence and its intrinsic
inverse and linearity fields. The adjacent value formulas and naturality laws
are stated separately in `SmoothPartFixedVectorsStatement` and proved in full
by `smoothPartFixedVectors` in `FixedVectorsProof.lean`.
The proof's validation reports a Lake build and exact-target,
statement-definition and frozen-input checks.
