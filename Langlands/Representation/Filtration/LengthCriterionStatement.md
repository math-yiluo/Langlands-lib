# Bounded chains and actual representation composition length

Worker 122 authored this statement pair from the target specification supplied
by Worker 170. Provenance: internal algebraic bridge.

`Langlands.ObjectCompositionLengthCriterion.{uK,uG,uV}` is a proposition
definition, with no proof of the proposition. For every field `k : Type uK`,
monoid `G : Type uG`, representation `A : Rep.{uV} k G`, and natural number
`b`, it conjoins the following two clauses:

1. `HasCompositionLengthAtMost A b` holds if and only if, for every natural
   number `m` and every strictly increasing map
   `c : Fin (m + 1) → Subrepresentation A.ρ`, one has `m ≤ b`.
2. `HasCompositionLengthAtMost A b` implies
   `IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule`.

The universes of the field, monoid, and representation carrier are independent.
There is no smoothness, admissibility, finite-dimensionality, or finite-length
premise. The algebra is the monoid algebra; when `G` is a group it is the
usual group algebra.

## Existing objects and boundary cases

The imported `Langlands.Representation.Filtration.ObjectDefinitions` supplies
the actual composition-series predicate. It means that there are a natural
number `n ≤ b` and an `ObjectRepFiltration A n` whose successive actual
quotient representations are irreducible. That filtration has `n + 1`
invariant subspaces, starts at zero, and ends at all of `A`. Irreducibility
includes nonzeroness. This module reuses those definitions unchanged.

The chain on the right side of the equivalence has `m + 1` terms and `m`
strict inclusions. Its endpoints are unrestricted: it need not start at zero
or end at all of `A`. In particular, the bound is not restricted to chains
that already have simple factors. This is a statement about invariant
subspaces and the monoid action, not about the dimension of the underlying
vector space.

All natural bounds are included. For `b = 0`, the right side excludes any
strict inclusion of invariant subspaces; since zero and the whole space are
invariant, this forces the representation to be zero. The existing
composition-series predicate also allows length zero, whose endpoint
conditions force the same conclusion. The zero representation is included;
the statement imposes no nontriviality assumption on its carrier.

## Relation to Mathlib

`Subrepresentation.subrepresentationSubmoduleOrderIso` in
`Mathlib.RepresentationTheory.Subrepresentation` identifies the invariant
subspaces of `A.ρ` with
`Submodule (MonoidAlgebra k G) A.ρ.asModule`, preserving their order.
Thus both sides concern the actual module determined by the action.

`CompositionSeries` in `Mathlib.Order.JordanHolder` is a finite series of
maximal steps in a lattice. On the submodule lattice those steps are covering
relations. Its length counts inclusions, and its definition does not require
bottom and top endpoints. A comparison with the Library's object
filtrations must therefore impose those endpoints and relate covering
relations to the irreducibility of the actual successive quotient
representations. The order isomorphism alone does not establish this
comparison.

`Mathlib.RingTheory.FiniteLength` defines `IsFiniteLength` by finite iterated
extensions of simple modules, including the zero module. Its theorem
`isFiniteLength_iff_exists_compositionSeries` characterizes this property by
a `CompositionSeries` of the module's submodule lattice with head bottom and
last top. It also provides
`isFiniteLength_iff_isNoetherian_isArtinian`. These are the relevant interfaces
for proving the second clause after constructing the comparison above.
Proving the uniform chain bound and its converse remains a separate proof
obligation. This module supplies the target for that work.

## Source motivation and scope

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), proof §2.14(2), printed page 449 / PDF page 10,
source ID `bernstein-zelevinsky-1977-induced-i`, original PDF SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original page was read directly for this statement.

In that argument an additive length measure built from Jacquet modules
is positive on every nonzero subquotient of the induced representation.
The authors use it to bound the representation's length. The present
criterion isolates an internal algebraic step needed to turn a uniform
bound on strict chains into the Library's existential composition-series
predicate and into module finite length.

The fully quantified field-and-monoid statement is a derived interface,
not a verbatim assertion of BZ77. It neither constructs the Jacquet-module
measure nor states or proves the cuspidal-induction theorem. No proof of
either clause of `ObjectCompositionLengthCriterion` is provided here.
