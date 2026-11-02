# Renard A.VIII.2: the module-category converse

Author: Worker 709.

This module states the categorical converse using an explicit witness:
the inverse image of the actual regular unital module. It contains no
proof of the converse.

## Exact statement and construction

In namespace `Langlands.Renard`,
`ModuleCategoryConverseStatement C R` is:

```lean
universe w v u r s

def ModuleCategoryConverseStatement
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : Type r) [Ring R] : Prop :=
  ∀ e : C ≌ ModuleCat.{max r s} R,
    HomSmallProgenerator.{w} (e.inverse.obj (ModuleCat.of R (ULift.{s} R)))
```

Here `R` is any unital ring, including noncommutative rings and the zero
ring. `ModuleCat` is Mathlib's category of unital left `R`-modules. The
regular module is `R` with its left multiplication action, lifted to
carrier universe `max r s` using `ULift.{s} R`. This is the same actual
object as in the published `RegularModuleSmallProgeneratorStatement`.
The chosen small progenerator of `C` is the actual object
`e.inverse.obj (ModuleCat.of R (ULift.{s} R))`.

The five universes are independent: `u` and `v` are the source object and
Hom universes, `r` is the ring universe, `s` is the lift universe, and `w`
is the coproduct index universe. In particular the source and target Hom
universes need not agree. The `max r s` bound merely ensures that the
regular module is an object of the target module category.

The only coproduct hypothesis is `HasCoproducts.{w} C`. The conclusion is
the published predicate in `C`, namely exactness, `w`-indexed coproduct
preservation and faithfulness of the actual integer-module Hom functor at
the displayed object. The statement imposes no separate coproduct
hypothesis on the module category: any needed instance can be transported
from `C` along the supplied equivalence.

No generator, enough projectives, Grothendieck or local finite-type
hypothesis is added. No substitute functor or assumed equivalence
conclusion is used; `e` is the categorical equivalence in the premise of
the converse.

## Source and derived realization

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix A.VIII.2, printed
page 267 / PDF page 273, the remark immediately after the
small-progenerator equivalence theorem. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read PDF273–274 in full for the audit underlying this unit.
The remark gives the converse because a unital ring is a small
progenerator of its category of unital modules. It supplies no proof.

The existence of a small progenerator in a category equivalent to modules
is the source assertion. The explicit inverse-regular-module witness,
the lifted carrier and the separate universe parameters are a derived
realization of that assertion. They are not additional wording attributed
to Renard. The formulation works at each specified coproduct index size;
it does not require a maximal-universe global coproduct hypothesis.
The supplementary 2010 errata, PDF pages 18–19, checked in the preceding
source audit, contain no correction to this converse remark.

For any supplied equivalence, a future proof of this target will also
give `∃ P : C, HomSmallProgenerator.{w} P` by taking the displayed inverse
image. The intended route is to transport coproduct existence to the
module category, use the published regular-module theorem, and transport
the small-progenerator predicate back along `e.symm`. These steps remain
proof obligations; the statement does not assume their conclusions.

## Scope

This target concerns ordinary unital left module categories. The forward
equivalence in the source uses right modules over an endomorphism ring,
implemented as left modules over its opposite; taking `R` to be an
opposite ring also gives that case here. Nonunital module categories
retain their separate definitions and obligations.

The regular-module theorem and the forward Hom-equivalence theorem
already have their own public statements and proofs. This unit supplies
the missing categorical converse target and makes no new proof or
whole-section completion claim.
