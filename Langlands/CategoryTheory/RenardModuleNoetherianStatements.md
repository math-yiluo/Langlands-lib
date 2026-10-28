# Renard's Noetherian comparisons for actual unital modules

This statement unit uses Mathlib's actual category of unital left modules
over an arbitrary unital ring. It states an object comparison and the
category/ring comparison in Renard's Appendix A.I.3. It proves neither.
The imported source-facing definitions in
`Langlands.CategoryTheory.RenardFiniteType` are unchanged.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Appendix A.I.2–A.I.3, printed248–249/PDF254–255, were read in full and
both pages were visually checked for this unit. The global convention at
printed6/PDF12 was also read: `M(A)` is the full category of unital
modules over a unital ring, even though the book elsewhere permits
nonunital rings and actions.

The current project source note
`notes/renard/appendix-a-corrections.md` and the published imported
definition pair were consulted. No dedicated Renard 2026 errata file was
found in the project or published notes. The registered supplementary
source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its PDF18–19 were read. Those pages do not address the A.I.3 wording
repairs described below; this is a limited check, and no author-issued
correction of the present example is claimed.

## Exact propositions and universes

All declarations are closed, transparent `def`s returning `Prop`, in
namespace `Langlands.Renard.ModuleNoetherian`. They use the independent
universe parameters `uR uM` in that order.

`ObjectStatement` binds

```lean
∀ (R : Type uR) [Ring R] (M : ModuleCat.{uM} R), ...
```

and states

```lean
Langlands.Renard.IsNoetherianObject M ↔ IsNoetherian R M
```

The left side says that every nonempty subset of the actual categorical
subobjects of `M` has a maximal element in that subset, in the existing
factorization order. It has no union-existence hypothesis. The right side
is Mathlib's algebraic Noetherian-module predicate: every ordinary left
`R`-submodule is finitely generated as an `R`-module. This object adapter
is an internal source-correspondence statement for Renard's Noetherian
definition; the source does not give this equivalence its own separate
number.

`CategoryStatement` binds `R : Type uR` and `[Ring R]`, and states

```lean
Langlands.Renard.IsNoetherianCategory (ModuleCat.{max uR uM} R) ↔
  IsNoetherianRing R
```

The left side is exactly the imported source convention: all subobject
unions exist, and every source-finite-type object is source-Noetherian.
It does not require every object of the module category to be Noetherian.
The right side is left Noetherianity of `R`, namely `IsNoetherian R R`
for the ordinary left regular module. This is the category/ring example
at printed249/PDF255, with its left-module convention made explicit.
Mathlib's different `CategoryTheory.Noetherian` predicate is not used.

The category target uses carrier universe `max uR uM`. It therefore
contains the lifted left regular module, for example the module on
`ULift.{uM} R`. This makes the converse to ring Noetherianity meaningful
without assuming that the ring is small in an unrelated lower carrier
universe. The object comparison retains completely independent `uR uM`;
it does not require the carrier to contain a copy of `R`. No
category/ring equivalence for arbitrary smaller carrier universes is
asserted.

`ModuleNoetherianStatement` is exactly
`ObjectStatement.{uR, uM} ∧ CategoryStatement.{uR, uM}`, in that order.
Both components bind every ring, instance and object internally.

## Scope and retained wording repairs

No component assumes commutativity, nontriviality, a field, finite
dimension, finite generation, countability or ring Noetherianity.
The last property occurs only as the right side of the category
equivalence. The zero ring and zero modules are included. All objects,
linear maps, submodules and categorical subobjects are the actual
Mathlib constructions; no surrogate action or subobject order is supplied.

The imported definitions retain the documented internal repairs to the
printed wording. A maximal element belongs to the given subset and need
not be greatest. Chains in the finite-type condition are nonempty;
properness is inequality with the top subobject, equivalently failure of
the inclusion to be an isomorphism. Arbitrary subobject unions include
the empty union. The separate finite-subcover comparison corrects the
printed cover equation to cover the object itself and allows an empty
finite subcover, as needed for zero. These repairs are documented
mathematical diagnoses, not author-issued errata.

The adjacent unital-module finite-type and finite-subcover comparisons
belong to task `c3a9b8fe-51c5-4e9f-98d1-d2a1aa238f96`. General
categorical maximal-subset, chain, sequence and all-subobjects-finite-type
comparisons remain separate. This unit neither supplies nor assumes
those results. Arbitrary nonunital-action categories and the unresolved
source convention for a nonunital Noetherian algebra remain separate as
well.

## Provenance and proof boundary

Renard cites [25], Proposition 1.6.1 and Lemma 3.6.1, near these examples,
and [37], 4.10 Theorem 1, for the preceding general compactness comparison.
Those bibliographic sources were not read for this unit and supply no
proof evidence here. This statement family uses the original 2026
passage and the unchanged published source-facing definitions.

The pinned Mathlib sources provide the actual order isomorphism
`ModuleCat.subobjectModule` and
`set_has_maximal_iff_noetherian` as possible proof-route ingredients.
They are not assumptions of these propositions or accepted proofs of
the exact aggregate. A separate proof successor must target the exact
published `ModuleNoetherianStatement` and verify its own dependencies,
including any finite-type comparison it uses.
