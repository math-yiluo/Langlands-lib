# Source finiteness and group-algebra finiteness for smooth representations

Worker 6. This statement unit isolates two comparisons needed to use the
categorical terminology in Renard III.1.4 with the Library's actual smooth
representations. It introduces no replacement category or finiteness convention.

## Exact targets

The declarations lie in `Langlands.SmoothRep`. Their parameters are a
commutative ring `R`, a group `G`, and a supplied topology on `G`. The
topological-group instance is quantified inside each component proposition.
The ring, group and representation-carrier universes `uR`, `uG` and `uV`
are independent.

| Declaration | Assertion for every actual `A : SmoothRep R G` |
| --- | --- |
| `RenardFiniteTypeStatement` | `Langlands.Renard.IsFiniteTypeObject A ↔ Module.Finite R[G] A.representation.asModule` |
| `RenardFiniteLengthStatement` | `Langlands.Renard.IsFiniteLength A ↔ A.HasFiniteLength` |
| `RenardFinitenessStatement` | The conjunction of those two complete, universally quantified propositions. |

On the categorical side, `IsFiniteTypeObject` retains existence of least
upper bounds for all subsets of the actual subobject type and the condition
that a nonempty chain of proper subobjects cannot have top as its least upper
bound. It is the unchanged source-facing predicate in
[`RenardFiniteType`](../../../Langlands/CategoryTheory/RenardFiniteType.md).
`Langlands.Renard.IsFiniteLength` retains existence of an actual finite
categorical composition chain with simple successive cokernels, as defined in
[`CompositionChains`](../../../Langlands/CategoryTheory/Renard/CompositionChains.md).

On the algebraic side, `R[G]` is the actual monoid algebra of the group.
`A.representation.asModule` is its existing unital module structure on the
representation carrier. `Module.Finite` means finite generation over this
group algebra. It permits infinite dimension over `R`: the generators and
their group translates span the representation. `A.HasFiniteLength` is the
unchanged predicate in [Basic](Basic.md), namely
`IsFiniteLength R[G] A.representation.asModule`. It concerns composition
length over the group algebra.

The assertions include zero objects. No nontriviality, finite dimension,
admissibility, Noetherianity, countability, local compactness, total
disconnectedness, or coefficient characteristic restriction is imposed.
There is no topology on the representation carrier.

## Source correspondence and provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The original passages read for these targets are:

- A.I.2–A.I.3, printed pages 248–249 / PDF254–255: actual categorical
  subobjects and unions, the finite-type chain condition, and the comparison
  between categorical finite type and finite generation in the unital module
  example. The imported predicate retains its documented explicit repairs,
  including nonempty chains and properness of the inclusion.
- A.VI.3, printed pages 263–264 / PDF269–270: composition chains, simple
  objects, finite length, and the simple-quotient assertions with the source
  category hypotheses.
- III.1.4, printed page 60 / PDF66: the transfer of this terminology to
  smooth representations through the Hecke-module equivalence, followed by
  the assertions about irreducible subquotients, finite-type quotients and
  finite-length subrepresentations.

These group-algebra comparisons are derived interface statements, not literal
formulas printed by Renard. The book works here with complex representations
of t.d. groups. The target deliberately extends the comparison to every
commutative coefficient ring and topological group. Its rationale is that
every invariant submodule of a smooth representation and its quotient are
again smooth, and the invariant-submodule order is the group-algebra
submodule order. Turning those existing constructions into the required
categorical subobject and composition-chain comparisons remains a proof
obligation. No such correspondence is assumed in the proposition.

The source's Hecke-module equivalence is not an input to these targets and is
not proved by them. A direct group-algebra proof would be an alternate route
to the same finiteness comparison. The independent universes and all actual
categorical subobjects must be retained in that proof, without an added
smallness hypothesis.

## Dependencies and status

The project imports are the existing
[abelian smooth category](Abelian.md), `RenardFiniteType`, and
`CompositionChains`. The statements reuse their actual objects and predicates.
The unital-module finite-type comparison in
`Langlands.CategoryTheory.RenardModuleFiniteTypeProof` is related reusable
mathematics; applying it alone does not establish the categorical comparison
for `SmoothRep`.

This file contains proposition definitions only. Neither comparison nor any
irreducible-existence assertion is proved here. Independent statement review
and publication must precede a separate exact-target proof. The three
III.1.4 existence assertions, with explicit nonzero hypotheses, and the
Hecke equivalence retain separate obligations.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.
