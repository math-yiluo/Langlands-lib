# Smoothing/completion correspondence and actual adjunction targets

This statement unit records the adjunction assertion of Renard I.1.5 for the
original nonunital actions and the actual smoothing and completion functors.
It defines three propositions and supplies interface checks. It proves no
Hom equivalence or adjunction.

## Original source and scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Chapter I conventions and I.1.1–I.1.5, printed pp.5–11/PDF11–17, provide the
original action convention, local units, nondegenerate part, compatible
LEFT-image families, coordinatewise completion maps and adjunction.
The I.1.5 proposition is on printed p.10/PDF16; its natural Hom
correspondence and displayed extension formula are on printed p.11/PDF17.

The scalar ring need not have an identity. An original action on an
abelian group has associativity and distributivity, with no identity-action
law even if the ring has an identity. `hA : IsIdempotented A` is the finite
local-unit condition. The source module `N` is an arbitrary ambient module;
only the target `M` has the nondegeneracy hypothesis in the universal
assertion. No commutativity, nontriviality, field, countability or dimension
condition is imposed. Zero rings and trivial groups are allowed.

## Per-action additive correspondence

`NonUnitalModuleSmoothingCompletionHomEquivalence hA N M` returns `Prop`
for `A : Type uA`, `N : Type uN` and `M : Type uM`, with independently sized
original data. It asserts existence of an additive equivalence

```
E : NonUnitalModuleHom A (nondegeneratePart hA N) M ≃+
      NonUnitalModuleHom A N (NonUnitalModuleLeftLimit A M).
```

The part carries the inherited original action and has its actual subtype
inclusion. The family carrier has precisely
`NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA`, selected inside the
proposition. Its coordinates satisfy the LEFT-image equations
`e • x(e) = x(e)` and `e • x(d) = x(e)` for `e ≤ d`.

The equivalence must have the coordinate extension formula
`(E f n).val e = f (e • n)`, with `e • n` bundled as an element of the
actual part. The subtype witness uses `e` and the original associativity
law together with `e * e = e`; this is only the membership proof needed
to type the target. No part vector is selected by a choice of local unit.
The second clause is an equality of entire original intertwiners:

```
(NonUnitalModuleLeftLimit.canonicalHom hA).comp (E.symm phi) =
  phi.comp (nondegeneratePart hA N).subtype.
```

Here the canonical map sends `m` to the family `e ↦ e • m`. Thus the
inverse is pinned to restriction followed by recovery through that
specific canonical map. Recovery, injectivity, surjectivity and an inverse
are conclusions or obligations of the correspondence; none is supplied
as a premise. `≃+` packages preservation of Hom addition in both directions.

Renard displays the Hom correspondence in the direction from ambient maps
into the completion to maps from the part. This target takes its inverse,
so extension is the forward map. Additive packaging and the whole-map
restriction identity are internal explicit forms of his natural
correspondence, using the source's pointwise Hom addition. The per-action
definition itself has no nondegeneracy premise; the master asserts it
under precisely `IsNondegenerate A M`.

## Actual categorical adjunction

`NonUnitalModuleSmoothingCompletionAdjunction.{uA,uV} hA` asserts existence
of the actual data

```
adj : nondegeneratePartFunctor.{uA, max uA uV} hA ⊣
        nondegenerateModuleCompletionFunctor.{uA, max uA uV} hA.
```

Smoothing is the published part functor on objects and actual restrictions
of original intertwiners on morphisms. Completion is the actual compatible
family functor restricted to nondegenerate source objects; its maps apply
the original intertwiner to every coordinate. Its target is the ambient
category, with no nondegeneracy assumption on the completion.

For every actual ambient object `N`, nondegenerate object `M`, original
part morphism `f`, vector `n` and idempotent `e`, the target requires
`adj.homEquiv N M f` to satisfy the same coordinate extension formula.
For every ambient completion morphism `phi`, it requires the same
whole-map inverse restriction identity on the underlying original
intertwiners, through `canonicalHom`. That clause also selects the named
family action explicitly. A final clause explicitly requires
`adj.homEquiv N M (f + g) = adj.homEquiv N M f + adj.homEquiv N M g`.
The `Adjunction` data include naturality in both variables and the unit,
counit and triangle identities for these actual functors.

The categorical vector universe is saturated to `max uA uV`: a compatible
family has carrier in `Type (max uA uV)`, and a further maximum with `uA`
has that same level. This makes the output and input ambient categories
agree without an equality assumption on `uA` and `uV`. The per-action
assertion retains all three independent universes and needs no saturation.
The earlier inclusion-left/part-right adjunction concerns a different
pair of functors from the pair stated here.

## Closed master and checks

`NonUnitalModuleSmoothingCompletionAdjunctionTheorem.{uA,uN,uM}` is closed
and returns `Prop`. For every original scalar ring and `hA`, it conjoins:

- The per-action assertion for every original `N : Type uN` and
  `M : Type uM`, with exactly `IsNondegenerate A M` as the module hypothesis.
- The actual categorical assertion at parameter `uV = max uN uM`, hence
  carrier universe `max uA (max uN uM)`.

The anonymous examples check the complete unapplied interfaces and exact
bodies of all three declarations at arbitrary independent universes and
both unequal scalar/vector assignments `(0,1)` and `(1,0)`. The master
body checks expand both subordinate propositions, including the specified
Hom groups, family action, extension/restriction identities and actual
adjunction. Further interface checks separate the source and target
universes. An explicit competing family action checks selection of the
prescribed action. Three same-carrier zero-action body checks cover the
source, target and both simultaneously; each retains the actual target
nondegeneracy hypothesis and adds no source nondegeneracy condition.
These checks are definitional typing checks, not proofs of the targets.

## Dependencies and remaining obligations

The entry imports `Langlands.Algebra.NonUnitalModuleCompletionFunctor`
and `Mathlib.CategoryTheory.Adjunction.Basic`. Its original part and
additive Hom structures come from the former's Library imports. Only this
new Lean/Markdown pair belongs to the focused statement unit. All action
and functor dependencies are imported from the published Library.

Independent statement acceptance and publication remain required after
the exact completion-functor dependency is public. A separate proof unit
must prove the closed master. Recovery/faithfulness, analytic completion,
the explicit uniform-completion equivalence, submodule closure and the
rest of I.1.5 remain separate obligations. This unit does not complete
I.1.5 or the whole book.

Authors: Worker 6 (statement definitions, Markdown and interface checks)
and Worker 1151 (source and installed-interface audit, fresh declaration
checks and submission preparation).
