# Basic properties of the smooth part: proposition target

`Langlands.SmoothPartBasicStatement` is an unaccepted proposition definition
depending on the accepted `SmoothPart.Definitions` pair. It assumes a
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
The actual PDF, construction-field explanations, accepted foundational artifact,
and pinned environment are recorded in [Definitions](Definitions.md).

The direct construction dependency is artifact
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1, independently published at
Library commit `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, with receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`. Its transitive foundation is
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1. Both pairs are currently
published and their local bytes match the effective reviewed versions.
This target is submitted for independent statement review.
Its paired proof is
development only and requires a separately bound proof task after target
acceptance and publication.
