# Object finiteness for original additive nonunital modules

Worker 6 prepared this statement-only adapter in namespace
`Langlands.Algebra.NonUnitalModuleFiniteness`; Worker 734 audited it
against the imported declarations and the original pages and submitted it.
It contains five closed transparent propositions and their ordered
conjunction. It proves none of them. The construction and predicates it
imports are unchanged.

## Objects, universes and the selected action

Every component internally binds

```lean
∀ (A : Type uA) [NonUnitalRing A] (M : NonUnitalModuleCat.{uA, uM} A), ...
```

The ring universe `uA` and carrier universe `uM` are independent, in that
order. The category is the published `Langlands.Algebra.NonUnitalModuleCat`
of additive commutative groups with actual possibly nonunital `A`-actions
and additive intertwiners. Every reference to the original action uses the
instance stored in `M`. The original ring may already have a unit, and its
unit may act by zero.

The first three right sides locally install exactly

```lean
CompatibleUnitization.module
  (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
```

as the `Module (Unitization ℤ A) M` instance. Integer scalars are the
canonical scalars of the additive group. An element `(n, a)` acts by
`n • m + a • m`, with the second term using the original action.
This is the same module as `IntegerUnitization.extendObj A M`.
No alternative action, module structure or action equation is an input,
and no global instance is introduced.

No component assumes a unit law for the original action, nondegeneracy,
commutativity, a field or complex-vector-space structure, nontriviality,
finite dimension, countability, finite generation or Noetherianity.
Zero rings, zero carriers and zero original actions are included.

## The five comparisons

All left sides refer to the actual categorical subobjects of `M` in
`NonUnitalModuleCat.{uA, uM} A`, with their factorization order. They use
the published source-facing predicates in `Langlands.Renard`, rather than
Mathlib's similarly named categorical predicates. They are instantiated
at the category's own sizes: objects in `Type (max uA (uM + 1))` and
morphisms, the additive intertwiners, in `Type uM`. Their quantifiers range
over subsets of the actual type `Subobject M`; no small representative
type is chosen.

| Declaration | Comparison |
| --- | --- |
| `FiniteTypeStatement` | `IsFiniteTypeObject M` iff `Module.Finite (Unitization ℤ A) M` for the selected action. |
| `FiniteSubcoverStatement` | `HasFiniteSubcoverProperty M` iff the same `Module.Finite` predicate. |
| `NoetherianStatement` | `IsNoetherianObject M` iff `IsNoetherian (Unitization ℤ A) M` for the selected action. |
| `FiniteGenerationStatement` | `IsFiniteTypeObject M` iff a finite set generates the whole carrier among the original stable additive subgroups. |
| `NoetherianGenerationStatement` | `IsNoetherianObject M` iff every original stable additive subgroup has a finite set of stable generators. |

The imported finite-type predicate includes existence of all subobject
unions and excludes top as the least upper bound of a nonempty chain of
proper subobjects. The finite-subcover predicate also includes union
existence, and each cover of top must contain a finite subcover, possibly
empty. The Noetherian predicate says that every nonempty subset of
categorical subobjects has a maximal member; it has no union-existence
premise. Properness is inequality with the top subobject, equivalently
failure of the inclusion to be an isomorphism. These are the wording
repairs already documented with `RenardFiniteType`; this adapter changes
none of them.

Every subgroup on the last two right sides is the actual
`NonUnitalSubmodule A M` for the stored original action, ordered by
inclusion of underlying subsets. It is an additive subgroup closed under
that action. In `FiniteGenerationStatement` the right side is exactly

```lean
∃ S : Finset M, ∀ P : NonUnitalSubmodule A M,
  (↑S : Set M) ⊆ P → ∀ m : M, m ∈ P
```

Thus every original stable additive subgroup containing the finite set
contains the whole carrier. In `NoetherianGenerationStatement` the right
side is exactly

```lean
∀ P : NonUnitalSubmodule A M,
  ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
    ∀ Q : NonUnitalSubmodule A M, (↑S : Set M) ⊆ Q → P ≤ Q
```

Here `P` is the smallest original stable additive subgroup containing
`S`. The set may depend on `P` and may be empty. Generation includes
addition, negation and zero, as well as the original action; it does not
mean generation by multiplication alone.

`NonUnitalModuleFinitenessStatement` is exactly the conjunction of the
five closed propositions in the table's order, with universe arguments
`.{uA, uM}` on every component. Each component binds its own inputs.

## Provenance and source correspondence

This is derived internal content, not a directly numbered source theorem.
The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its retained file is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 6 reread saved direct extracts of printed5–6/PDF11–12,
printed14/PDF20 and printed248–249/PDF254–255 for this adapter. The
parent's earlier reading also visually checked PDF254–255. For the audit,
Worker 734 confirmed the file's SHA256 and re-extracted the text of these
five pages from it.

The Chapter I conventions permit nonunital rings and nonunital actions
even over a unital ring. A.I.2 defines categorical subobjects and their
factorization order. A.I.3 defines the finite-type and Noetherian
conditions. Its module example concerns the category `M(A)` of ordinary
unital modules over a unital ring. The published
`RenardModuleFiniteTypeStatements` and `RenardModuleNoetherianStatements`
express that example using `ModuleCat`.

The present targets instead concern the whole additive nonunital-action
category. The intended proof route transfers the categorical conditions
through the actual subobject comparison and the published integer
unitization equivalence, then uses the unital-module comparisons and
the original-action generation comparisons. These are proof ingredients,
not extra hypotheses or proofs supplied here. The comparison
`Subobject M ≃o NonUnitalSubmodule A M` is owned by task
`e0c2f2dc-19ea-4590-8f21-681193c6b15c`, and the proof of
`IntegerOriginalSubmoduleGenerationStatement` by task
`1ac1f4eb-ccc6-4bba-afa5-e120455acbc1`; neither was public when this
statement was prepared.

Renard's I.2.1 adjoins a complex unit to a complex algebra whose modules
are also complex vector spaces. Integer unitization here is an internal
choice for arbitrary additive groups. This module does not assert that
integer unitization gives the source's complex-linear category or fixes
the source's convention for a possibly nonunital Noetherian algebra.

Worker 6 also reread the relevant saved extract of PDF18–19 of the
registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its correction to old printed314 requires extra complex-vector-space
data. Those pages do not give these integer categorical comparisons or
correct the A.I.3 wording. The 2026 text governs. The published
`notes/renard/appendix-a-corrections.md` concerns other passages. No
dedicated 2026 Renard errata file was found in the parent audit.
Renard's references [25] and [37] have not been read for this adapter
and supply no proof evidence here.

## Scope

The subobject construction belongs to its separate definition task;
these statements assume no order isomorphism as an input and do not
reimplement one. Existing category and algebraic-generation units retain
their interfaces. A proof successor must target the exact published
aggregate and use independently published dependencies.

This object comparison keeps `uA` and `uM` independent. A category/ring
criterion involving a regular module requires separate size treatment
and is not stated here. Canonical complex scalar recovery, the
nondegenerate-module category, abelianness, exactness, adjoints, tensor
products, full C.II and the other book assertions remain separate.
