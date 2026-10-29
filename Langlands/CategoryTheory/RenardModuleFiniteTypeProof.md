# Proof of Renard's finite-type example for actual unital modules

This module proves the published closed statement
`Langlands.Renard.ModuleFiniteType.ModuleFiniteTypeStatement.{uR, uM}` from
`Langlands.CategoryTheory.RenardModuleFiniteTypeStatements`. The exported
theorem is

```lean
theorem Langlands.Renard.ModuleFiniteType.moduleFiniteType :
    ModuleFiniteTypeStatement.{uR, uM}
```

with universe parameters `uR uM` and no other parameters. The statement
pair and everything it imports are used unchanged.

## Setting

`R : Type uR` is an arbitrary unital ring, possibly noncommutative and
possibly the zero ring, and `M : ModuleCat.{uM} R` is an object of
Mathlib's actual category of unital left `R`-modules. The universes `uR`
and `uM` are independent. Subobjects are Mathlib's actual
`CategoryTheory.Subobject M` with its factorization order. No finite
generation, Noetherianity, countability, nontriviality or field hypothesis
is used.

The proof transports order-theoretic facts along Mathlib's order
isomorphism `ModuleCat.subobjectModule M : Subobject M ≃o Submodule R M`.
This is a proof tool. The source predicates are not replaced by
submodule-lattice conditions.

## Union existence

`hasSubobjectUnions M` proves `HasSubobjectUnions M`. For a set `S` of
subobjects, the supremum of its image in the complete lattice
`Submodule R M` is a least upper bound there. Its preimage under the order
isomorphism is a least upper bound of `S`, by `OrderIso.isLUB_image`. The
empty set is included.

## Finite subcovers and finite generation

`finiteSubcover_iff_finite M` proves
`HasFiniteSubcoverProperty M ↔ Module.Finite R M`. By `Module.finite_def`
and `Submodule.fg_iff_compact`, finite generation of `M` is compactness of
the top submodule. Mathlib's
`isCompactElement_iff_exists_le_sSup_of_le_sSup` describes compactness as:
every set of submodules whose supremum is at least top has a finite subset
whose supremum is at least top.

- Forward: given submodules covering top, map them to subobjects. The image
  set has least upper bound top, because the order isomorphism preserves
  least upper bounds. The source finite-subcover property gives a finite
  subset of the image with least upper bound top. Its image under the
  isomorphism is a finite subset of the original submodules whose supremum
  is top.
- Reverse: union existence is `hasSubobjectUnions M`. Given a set `S` of
  subobjects with least upper bound top, its image in `Submodule R M` has
  supremum top. Compactness gives a finite subset of the image with
  supremum top. Mapping it back gives a finite subset of `S` with least
  upper bound top.

Membership of the transported finite sets in the original cover is checked
through `Finset.mem_image`. The finite subsets may be empty, as the source
predicate allows. For example, the zero module has the empty finite
subcover.

## Finite type and finite generation

`finiteType_iff_finite M` proves `IsFiniteTypeObject M ↔ Module.Finite R M`.
It applies the general theorem
`Langlands.Renard.finiteTypeFiniteSubcover (ModuleCat.{uM} R)`, which
proves `Langlands.Renard.FiniteTypeFiniteSubcoverStatement` in an arbitrary
category, at the object `M`. This gives
`IsFiniteTypeObject M ↔ HasFiniteSubcoverProperty M`, which is then
composed with `finiteSubcover_iff_finite M`. The general chain-to-cover
argument is reused, not reproved here.

## Closed theorems

`finiteType : FiniteTypeStatement.{uR, uM}` and
`finiteSubcover : FiniteSubcoverStatement.{uR, uM}` introduce `R`, its ring
instance and `M`, and apply the two comparisons. `moduleFiniteType` is the
ordered pair `⟨finiteType, finiteSubcover⟩`. These closed theorems are
stated outside the section declaring `R` and `M`, so they have no section
parameters.

## Source correspondence

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The first sentence of the `Exemple` closing A.I.3, printed page 249 / PDF
page 255, says that a module over a unital ring is of finite type in `M(A)`
exactly when it is finitely generated. It cites [25], Lemma 3.6.1. The
preceding compactness paragraph, printed pages 248–249 / PDF pages 254–255,
characterizes finite
type by finite subcovers and cites [37], 4.10 Theorem 1. Neither cited
book was read. The implemented proof is an alternate route through
Mathlib's subobject–submodule order isomorphism and the general
categorical theorem above. It does not claim to reproduce the cited proofs.

The internal repairs documented with the statement and its imported
predicates are retained unchanged: properness is inequality with top,
chains are nonempty, finite subcovers may be empty, and the printed
initial cover equation is read with the ambient object. These are not
author-issued errata.

## Scope

This module concerns Mathlib's `ModuleCat R`, which is the source category
`M(A)` of unital modules. It does not construct or compare the larger
category of possibly nonunital actions. The Noetherian half of the
`Exemple`, general categorical Noetherian criteria, action, Hom, lattice,
restriction and quotient constructions, localization and the final C.II
proposition remain separate obligations.

## Provenance

Worker 709 wrote the proofs of `hasSubobjectUnions` and
`finiteSubcover_iff_finite` in shared draft revision 1 of this task.
Worker 820 added the finite-type comparison through the general theorem,
the closed theorems and this Markdown. The general theorem
`Langlands.Renard.finiteTypeFiniteSubcover` is Worker 6's separate,
already published work in the Library module
`Langlands.CategoryTheory.Renard.FiniteTypeFiniteSubcover`; it is imported
unchanged and is not part of this contribution.
