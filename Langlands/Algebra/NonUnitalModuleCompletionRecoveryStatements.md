# Recovery and faithfulness of actual module completion: statements

Authors: Worker 6 (statement draft and interface checks) and Worker 185
(source and interface audit). The governing original is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Chapter I conventions and I.1.1–I.1.5, printed
pp.5–11/PDF11–17. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The recovery assertion and equations (I.1.5.1)–(I.1.5.2) occur at
printed p.10/PDF16; faithfulness is proved at the start of
printed p.11/PDF17.

## Exact constructions and source correspondence

This file states the first two clauses of the proposition in I.1.5 over
the actual original nonunital-module categories and compatible left-image
families. It imports `NonUnitalModuleCompletionFunctor`, which supplies
the actual restricted completion functor and the named family action.
The original vector `m` has canonical family `e ↦ e • m`. The
nondegenerate part is the existing stable additive subgroup of elements
fixed by some actual idempotent.

Renard first identifies completion with `Hom_A(A,M)` and sends `m` to
the homomorphism `a ↦ a • m` in (I.1.5.1). Evaluating at each
idempotent gives precisely the imported canonical family map. The
source then shows that a homomorphism fixed by `e` is the canonical
homomorphism of its value at `e`, and concludes (I.1.5.2).
The present family formulation records that same comparison directly
on the actual family carrier. It does not assume a Hom comparison,
an inverse map, bijectivity or part recovery as input.

## Recovery target

`NonUnitalModuleCompletionPartRecovery hA M` is a proposition about
the specified original action on `M`. It first selects
`NonUnitalModuleLeftLimit.nonUnitalModule hA` on
`NonUnitalModuleLeftLimit A M`. Every occurrence of the nondegenerate
part and every family scalar multiplication in its body uses this
named action, including when another family action is in scope.

The conclusion is the existence of an actual additive equivalence

```text
E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M).
```

Three simultaneous requirements specify this equivalence. The entire
additive composite of `E` with the actual submodule inclusion equals
`NonUnitalModuleLeftLimit.canonical`; this is an equality of additive
maps, not only a pointwise or abstract isomorphism assertion.
For every original scalar `a` and vector `m`,
`E (a • m) = a • E m`, with the inherited action on the actual part.
Finally, for every part element `x` and every actual idempotent `e`
fixing its underlying family under the named action,

```text
E.symm x = x.val.val e.
```

The last requirement applies to every fixing idempotent, without
choosing one as part of the input. It exposes the evaluation argument
in the source. The existence packaging, explicit action selection,
entire-map equation, equivariance and universal coordinate inverse
formula are internal specifications of the source's canonical
identification.

The per-action proposition describes the conclusion. The closed
theorem target asserts it only under `IsNondegenerate A M`, as in
the source. In particular, arbitrary ambient zero actions are not
asserted to satisfy recovery without that hypothesis.

## Faithfulness and the closed theorem target

`NondegenerateModuleCompletionFaithful.{uA,uM} hA` is definitionally
the `Faithful` property of the actual functor

```text
nondegenerateModuleCompletionFunctor.{uA,uM} hA :
  NondegenerateModuleCat.{uA,uM} A ⥤
    NonUnitalModuleCat.{uA,max uA uM} A.
```

The imported functor extends each actual intertwiner coordinatewise:
its value at `x` has coordinate `f(x(e))`. No abstract replacement
functor or faithfulness premise is used. Renard proves that a completed
map equal to zero has original map zero. The categorical `Faithful`
property states injectivity on each actual Hom set; this is the
standard equivalent formulation in these additive categories.

`NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{uA,uM}` is
a closed `Prop`. It quantifies over every original nonunital ring `A`
and `hA : IsIdempotented A`, then conjoins recovery for every original
nondegenerate module `M` with faithfulness of the actual restricted
functor. All algebraic structures and hypotheses appear in its body.
The additive equivalence, equivariance, inverse formula and faithfulness
are conclusions only.

## Universes and interface checks

The scalar and vector universes `uA` and `uM` are independent.
The actual family carrier, and therefore its nondegenerate part, lie
in `Type (max uA uM)`. An additive equivalence to the original `M`
is allowed across those universes; no carrier replacement or equality
of universes is imposed.

Complete unapplied interfaces are checked at arbitrary universes and
at `(uA,uM) = (0,1)` and `(1,0)`. Exact-body equations check the
recovery conclusion, faithfulness against the constructed functor and
the full closed target at arbitrary universes and both unequal numeric
assignments. Another exact-body check installs a competing
family action before unfolding recovery and verifies that the named
action remains selected. The same-carrier zero-action check uses the
original `NonUnitalModule.zero` action on `A`, retains its actual
`IsNondegenerate A A` hypothesis and checks the full recovery conclusion
under the separately selected family action.

No original identity-action law, commutativity, nontriviality,
countability, field or dimension hypothesis is added. Zero rings and
trivial carriers remain permitted.

## Status and boundaries

These are proposition definitions and interface checks. The file proves
neither recovery nor faithfulness. The exact-target proof is a separate
unit after independent statement acceptance and publication. The
smoothing/completion adjunction, topological completion comparison and
submodule-closure assertion (I.1.5.3) remain separate obligations.
The existing inclusion-left/nondegenerate-part-right coreflection has
a different orientation and establishes neither assertion here.
This unit does not finish I.1.5 or the whole-book program.
