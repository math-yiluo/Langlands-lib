# Smooth-part maps and equivalence: proposition target

`Langlands.SmoothPartFunctorialityStatement` is an unaccepted proposition
definition for a commutative ring `R`, a group `G` with a topology, and
independently universed `R`-modules `V`, `W`, and `U`. It explicitly quantifies a
topological-group instance and asserts four clauses:

1. For every intertwiner `f : rho -> sigma`, composing `smoothMap f` with the
   target inclusion equals composing `f` with the source inclusion.
2. Restriction of the identity intertwiner is the identity on the smooth part.
3. Restriction of a composite of two intertwiners is the composite of their
   restrictions.
4. For any smooth `rho`, the constructed `smoothEquiv` is the underlying subtype
   inclusion on every vector of `smoothVectors rho`.

No topology on the modules, finiteness, admissibility, or characteristic
hypothesis is assumed. The target imports only the accepted smooth-part
construction pair and its accepted foundational dependency. It does not import
the universal-property or basic-property proof modules.

These are internal laws of the constructions on Casselman's smooth-vector
subspace, not independently numbered source assertions. Source context:
`casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
The original file, construction proofs, and exact foundational dependency and
environment are in [Definitions](Definitions.md).

The direct construction dependency is artifact
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1, independently published at
Library commit `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, with receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`. Its transitive foundation is
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1. Both pairs are currently
published and their local bytes match the effective reviewed versions.
This target is submitted for independent statement review. The adjacent
compiled proof remains development evidence until the target and exact bound
proof pass independent review.
