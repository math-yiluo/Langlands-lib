# Proof of the twist subquotient laws

Worker 4 authored this internal derived proof. It imports the published statement
and the existing Mathlib irreducibility interface.

The underlying-submodule formula and the two vector formulas are definitional
equalities. The bottom, top, sum and intersection identities use the standard
mapping laws of `twistSubrepresentationOrderIso`. Simplicity of the lattice
is transported by `OrderIso.isSimpleOrder_iff`. The closing theorem packages
these eight results as the entire `Langlands.TwistSubquotientLaws` target,
with the original coefficient, group and module universes.

The final reusable corollary `isIrreducible_twist_iff` specializes to a field.
It follows directly because Mathlib's `Representation.IsIrreducible` is
the same simple-order predicate on the subrepresentation lattice. In
particular, no new irreducibility predicate is introduced and the zero-space
case is not accidentally included as irreducible.

This proof uses no topological or finite-dimensional hypotheses. It does not
claim that a classification, finite-length theorem or LLC has been proved.

## Declarations

All declarations are in the namespace `Langlands`. The first eight prove,
in order, the eight conjuncts of the target. They are stated for a commutative
ring `R`, a group `G` and an `R`-module `V`, with the character `chi : G →* Rˣ`
and the representation or subrepresentations as arguments.

1. `twistSubrepresentation_toSubmodule`, simp lemma proved by `rfl`.
2. `twistSubrepresentation_bot`, simp lemma from `OrderIso.map_bot`.
3. `twistSubrepresentation_top`, simp lemma from `OrderIso.map_top`.
4. `twistSubrepresentation_sup`, simp lemma from `OrderIso.map_sup`.
5. `twistSubrepresentation_inf`, simp lemma from `OrderIso.map_inf`.
6. `twistSubrepresentationEquiv_apply`, simp lemma proved by `rfl`.
7. `twistQuotientEquiv_mkQ`, simp lemma proved by `rfl`.
8. `isSimpleOrder_twist_iff`, the symmetric form of `OrderIso.isSimpleOrder_iff`
   for `twistSubrepresentationOrderIso chi rho`.

Each of the four lattice laws is the corresponding `OrderIso` law applied to
`twistSubrepresentationOrderIso chi rho`, whose forward map is
`twistSubrepresentation chi`. The three `rfl` proofs hold because the
constructions retain the same submodule and use identity linear equivalences.

`twistSubquotientLaws` introduces `chi` and `rho` and returns the tuple of
these eight facts. `isIrreducible_twist_iff` is stated for a field `K`, with
the same universe pattern, and is proved by `isSimpleOrder_twist_iff`.
In `Mathlib/RepresentationTheory/Irreducible.lean`,
`Representation.IsIrreducible rho` is the abbreviation
`IsSimpleOrder (Subrepresentation rho)`. Mathlib states it for a monoid;
here the group `G` supplies that monoid.

## Exact development boundary

The target is the Library declaration `Langlands.TwistSubquotientLaws` in
`Langlands.Representation.Twist.SubquotientStatement`. Its published
construction dependency is
`Langlands.Representation.Twist.SubquotientDefinitions`, based on
`Langlands.twist` in `Langlands.Representation.Twist.Definitions`.
The proof imports these modules without changing the target or its dependencies.

The provenance is the internal order-equivalence construction described above.
Independent semantic review accepted this proof contribution. Compilation
and exact-type development checks are separate evidence.

## Development checks

Worker 67 adopted Worker 4's Lean source unchanged and expanded this
explanation. The workspace's `Langlands` tree was identical to Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. The environment was
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0; Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). The module compiled with no
errors or warnings.

Inspection reported `Langlands.twistSubquotientLaws` as a theorem with
level parameters `uR`, `uG` and `uV`. Its unapplied type is
`∀ {R : Type uR} {G : Type uG} {V : Type uV} [CommRing R] [Group G]
[AddCommGroup V] [Module R V], TwistSubquotientLaws`. This is the complete
outer telescope of the target. A separate check file assigned the unapplied
constant `@Langlands.twistSubquotientLaws` to that telescope without adapting
arguments. Both the closing theorem and `isIrreducible_twist_iff` depend only
on `propext`, `Classical.choice` and `Quot.sound`. These are development
checks, not independent acceptance.
