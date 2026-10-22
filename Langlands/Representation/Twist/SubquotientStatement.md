# Lattice and underlying-map laws for character-twisted subquotients

`Langlands.TwistSubquotientLaws` is a proposition definition for arbitrary
commutative coefficient rings, groups and modules in three independent
universes. It quantifies a unit-valued character and a representation and
asserts eight related facts about the constructions in
`Langlands.Representation.Twist.SubquotientDefinitions`:

1. Twisting a subrepresentation retains its underlying submodule.
2. It preserves the bottom subrepresentation.
3. It preserves the top subrepresentation.
4. It preserves binary sums.
5. It preserves binary intersections.
6. The restriction equivalence acts as the identity on each vector.
7. The quotient equivalence sends the class of each vector to the same class.
8. The twisted subrepresentation lattice is a simple order exactly when
   the original lattice is.

The sum and intersection use the existing Mathlib lattice on
`Subrepresentation`; they do not assert equality of representations on
different carrier types. The last assertion uses `IsSimpleOrder`, which
includes nontriviality of the bounded order, so it does not incorrectly
classify the zero representation as simple. Over a field this is exactly
Mathlib's `Representation.IsIrreducible`, rather than a new irreducibility
predicate. The proof module supplies that field-specialized corollary.

There are no topology, smoothness, admissibility, finite dimension or
Noetherian assumptions. The target does not assert finite-length
classification or a local Langlands correspondence.

## Provenance and dependency status

This is an internal family of laws for the identity-on-submodule twist
construction, not a theorem attributed to external literature. The
simple-order assertion follows from its order equivalence, and the two
vector formulas describe its identity linear maps.

The constructions in `Langlands.Representation.Twist.SubquotientDefinitions`
are independently accepted and published in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`. Their base is `Langlands.twist`
in `Langlands.Representation.Twist.Definitions`. Both construction files
and all imported project sources match those used for the compiled draft.
The final semantic review and final Lake/declaration checks were inspected.

The pinned source `Mathlib/Order/Atoms.lean` provides the existing
simple-order predicate and its transport under an order equivalence.
`Mathlib/RepresentationTheory/Irreducible.lean` defines irreducibility
over a field as the simple-order predicate on `Subrepresentation`.
Neither source is replaced by a project-specific copy.

Worker 4 authored this paired statement in environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
No independent statement or proof acceptance is claimed.
