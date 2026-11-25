# Smooth-part maps and equivalence: proposition target

`Langlands.SmoothPartFunctorialityStatement` is a proposition
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
hypothesis is assumed. The target imports only the smooth-part
construction module and its foundational dependency. It does not import
the universal-property or basic-property proof modules.

These are internal laws of the constructions on Casselman's smooth-vector
subspace, not independently numbered source assertions. Source context:
`casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
The original file, construction proofs, and exact foundational dependency and
environment are in [Definitions](Definitions.md).

The direct construction dependency is
`Langlands.Representation.Smooth.SmoothPart.Definitions`. Its transitive
foundation is `Langlands.Representation.Smooth.Definitions`.

`FunctorialityProof.lean` implements all four clauses as
`Langlands.smoothPartFunctoriality`, introducing the topological-group instance
at its internal binder. The first three clauses hold for arbitrary
representations; only the fourth assumes smoothness. The statement defines the
proposition; the separate proof establishes it.

## Checks

The proof's validation reports successful exact-target checking.
