# Proof: source axioms for Renard's full module categories

Worker 709 wrote this proof. Worker 937 rechecked it and edited this
Markdown for submission. The module
`Langlands.Algebra.RenardFullModuleAxiomProof` proves the published closed
target
`Langlands.Algebra.RenardFullModuleAxiomStatements.FullModuleAxiomsStatement`
as the theorem `fullModuleAxioms`. Its level parameters `uA`, `uI` and `uM`
are the same as the statement's. The statement Markdown
`Langlands/Algebra/RenardFullModuleAxiomStatements.md` records the source
correspondence, the selected abelian structures and the meaning of each
component. This file describes the implemented Lean proof.

## Source and route

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c` (hash
recomputed). Printed p.263 / PDF269 defines source AB5 and AB6. The
"Exemples" paragraph at the top of printed p.264 / PDF270 asserts that
`A-mod` for a ring `A` and `M(A)` for a unital ring `A` satisfy all these
axioms. The source gives no proof. As in the statement Markdown, `A-mod` over an
arbitrary ring is read as the full category `NonUnitalModuleCat A` of
original additive actions, and `M(A)` over a unital ring as Mathlib's
`ModuleCat A`. The proof below uses its own route. It is the standard
argument: categorical subobjects are submodules, submodule lattices are upper
continuous, cyclic submodules are finitely generated, and module categories
have coproducts. It adds no hypothesis to any of the six components. It proves
exactly the six components of the statement: coproducts (source AB4*), the
directed law (source AB5) and local finite type (source AB6). It makes no
claim about products (source AB4) or Mathlib's `AB5OfSize`, which the
statement does not include.

Every comparison between categorical subobjects and submodules used here is
either already published (Mathlib's `ModuleCat.subobjectModule`,
`Subobject.subobjectOrderIso` and `Submodule.mapIic`, and the published
`NonUnitalModuleFiniteness.subobjectExtendOrderIso`) or constructed in this
file from those (`iicOrderIso`, `subobjectSubmoduleOrderIso` and the
composite inside `finiteType_of_fg`). None is assumed.

## Generic transport lemmas

Section `Transport` fixes a category `C`, with no abelian or other
hypothesis, a ring `R` and an `R`-module `V`.

- `iicOrderIso e x : Set.Iic x ≃o Set.Iic (e x)` restricts an order
  isomorphism to lower intervals.
- `directedSums_of_orderIso e F hF N`: let `α` be a meet-semilattice with
  `e : α ≃o Submodule R V`, and let `F : I → α` be a directed family over
  any `I : Type uI` (it may be empty). Then the element
  `U := e.symm (⨆ i, e (F i))` is a least upper bound of `Set.range F`, and
  `N ⊓ U` is a least upper bound of the family `N ⊓ F i`. The first claim
  transports `isLUB_iSup` through `OrderIso.isLUB_image`. For the second,
  `e` preserves meets (`map_inf`). Mathlib's `Directed.inf_iSup_eq` holds in
  every compactly generated lattice, which includes `Submodule R V`. It
  gives `e N ⊓ ⨆ i, e (F i) = ⨆ i, e N ⊓ e (F i)`, and `isLUB_iSup` is
  transported back through `OrderIso.isLUB_image'`.
- `finiteType_of_fg e P hP`: let `e : Subobject X ≃o Submodule R V`. If
  `e P` is finitely generated, then `(P : C)` satisfies the published source
  predicate `Langlands.Renard.IsFiniteTypeObject`. The proof composes
  Mathlib's `Subobject.subobjectOrderIso P` (subobjects of `(P : C)` are the
  interval `Set.Iic P`), `iicOrderIso e P`, the inverse of
  `Submodule.mapIic (e P)` and the inverse of
  `ModuleCat.subobjectModule (ModuleCat.of R (e P))`. The result is an order
  isomorphism from `Subobject (P : C)` to the subobjects of the module
  `ModuleCat.of R (e P)`. That module is finite by `Module.Finite.iff_fg`.
  Hence it is source finite type by the published
  `Langlands.Renard.ModuleFiniteType.finiteType_iff_finite`. The published
  `Langlands.Renard.finiteTypeFiniteSubcover` turns this into the
  finite-subcover property, which
  `NonUnitalModuleFiniteness.hasFiniteSubcoverProperty_of_orderIso`
  transports to `(P : C)`. `finiteTypeFiniteSubcover` then turns it back.
- `locallyFiniteType_of_orderIso e`: if `e : Subobject X ≃o Submodule R V`,
  then `X` satisfies the published
  `Langlands.Renard.IsLocallyFiniteTypeObject`, so `⊤` is the least upper
  bound of the finite-type subobjects. `⊤` is an upper bound by `le_top`.
  Let `Q` be any upper bound and `x : V`. The subobject
  `e.symm (Submodule.span R {x})` is finite type by `finiteType_of_fg` and
  `Submodule.fg_span_singleton`, so it lies below `Q`. Applying `e` shows
  that `x ∈ e Q`. Therefore `e Q = ⊤`, and `Q = ⊤` because `e` reflects the
  order and preserves `⊤`.

## Nonunital components

For a nonunital ring `A : Type uA` and `M : NonUnitalModuleCat.{uA, uM} A`,
`subobjectSubmoduleOrderIso M` is an order isomorphism from `Subobject M` to
the submodules of the published integer-unitized module
`IntegerUnitization.extendObj A M` over `Unitization ℤ A`. It composes the
published `NonUnitalModuleFiniteness.subobjectExtendOrderIso M` with
Mathlib's `ModuleCat.subobjectModule`. The subobjects here are those of the
category `NonUnitalModuleCat`. They do not depend on the abelian instance
that the statements select.

- `nonUnitalDirectedSubobjectDistributivity` applies
  `directedSums_of_orderIso` to `subobjectSubmoduleOrderIso M`.
- `nonUnitalSourceAB5`: the directed clause is the previous theorem at
  carrier universe `max uI uM`. For coproducts, every `J : Type uI` has
  `HasColimitsOfShape (Discrete J)` in
  `NonUnitalModuleCat.{uA, max uI uM} A`. Mathlib's
  `Adjunction.hasColimitsOfShape_of_equivalence` pulls these back along the
  published equivalence `IntegerUnitization.extendFunctor A`, whose
  `IsEquivalence` instance is published. Mathlib's colimit instance supplies
  the coproducts in `ModuleCat.{max uI uM} (Unitization ℤ A)`.
- `nonUnitalSourceAB6` applies `locallyFiniteType_of_orderIso` to
  `subobjectSubmoduleOrderIso M`.

## Unital components

For a ring `A : Type uA` and `M : ModuleCat.{uM} A`, Mathlib's
`ModuleCat.subobjectModule M : Subobject M ≃o Submodule A M` plays the same
role.

- `unitalDirectedSubobjectDistributivity` applies
  `directedSums_of_orderIso` to it.
- `unitalSourceAB5` takes the coproducts in `ModuleCat.{max uI uM} A` from
  Mathlib's colimit instances by `inferInstance`. Its directed clause is
  the previous theorem at carrier `max uI uM`.
- `unitalSourceAB6` applies `locallyFiniteType_of_orderIso` to it.

## Aggregate

`fullModuleAxioms` is the anonymous-constructor conjunction of the six
theorems, in the order of `FullModuleAxiomsStatement`. Four closing
`example`s instantiate it at the generic levels and at the concrete level
triples `0, 1, 0`, `1, 0, 2` and `2, 1, 0`.

## Checks

Diagnostic `84b19b6a-0671-4f01-acdb-dfa8acc27639` (Worker 709) compiled the
module with a Lake build in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with zero errors and zero warnings.
It inspected `fullModuleAxioms`, a theorem with level parameters `uA`, `uI`
and `uM`. Its axioms are only `propext`, `Classical.choice` and `Quot.sound`.
There is no `sorry` and no new axiom.

Worker 937 repeated the build and inspection against Library commit
`83773f62c5adf54634640cbfaf89822a74b44700` (diagnostic
`d9e5ac61-abac-45a4-9dbe-25d23ce7f267`, same results), and again on the
submitted workspace (diagnostic `2ec28662-911a-4136-9e2f-d0e0650bc9d4`,
same results). A separate private
probe, not part of this unit (diagnostic
`c92d54bb-db30-4cee-aafe-16cc4c2f43b1`), checked
`type_of% fullModuleAxioms.{uA, uI, uM} = FullModuleAxiomsStatement.{uA, uI, uM}`
by `rfl`. It also instantiated the theorem at permuted and mixed levels and
extracted three unfolded components: source AB6 for
`NonUnitalModuleCat.{0, 2} ℤ`, source AB5 for `ModuleCat` over the zero ring
`PUnit`, and the directed law for an arbitrary `ModuleCat.{uM} A`. All
compiled without diagnostics.
