# Basic properties of the smooth part: proposition target

`Langlands.SmoothPartBasicStatement` is a proposition definition
depending on `SmoothPart.Definitions`. It assumes a
commutative ring `R`, a group `G` with a topology, and an `R`-module `V`, in
independent universes.

For every representation `rho`, it asserts:

1. Membership in `smoothVectors rho` is equivalent to `IsSmoothVector rho`.
2. Zero is smooth.
3. The sum of any two smooth vectors is smooth.
4. Every scalar multiple of a smooth vector is smooth.
5. `rho` is smooth if and only if `smoothVectors rho` is the whole module.
6. For every topological-group instance on `G`, smooth vectors are invariant
   under each group element, `smoothPart rho` is smooth, and its inclusion is
   the underlying subtype map and is injective.

The final group of clauses explicitly quantifies `IsTopologicalGroup G` inside
the proposition. The earlier clauses do not require this compatibility between
the group operations and topology. No topology on `V` or finiteness hypothesis
is present.

The membership and closure clauses express the actual smooth-vector submodule
described by Casselman; the smoothness characterization and properties of the
restricted representation are internal consequences of that construction.
They are not quoted as a separately numbered source theorem.

Exact source: `casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
The actual PDF, construction-field explanations, foundational dependency,
and pinned environment are recorded in [Definitions](Definitions.md).

The direct construction dependency is
`Langlands.Representation.Smooth.SmoothPart.Definitions`. Its transitive
foundation is `Langlands.Representation.Smooth.Definitions`.

`BasicProof.lean` implements the entire target as `Langlands.smoothPartBasic`.
It supplies the unrestricted clauses first and introduces `IsTopologicalGroup`
only at the final conjunct's internal binder. The statement defines the
proposition; the separate proof establishes it.

## Checks

The proof's validation reports successful exact-target checking, beyond
source presence and development compilation.
