# The completion of the nondegenerate dual is the full dual (Renard I.4.3): proof

Module `Langlands.Algebra.NonUnitalModuleDualCompletionProof`, namespace
`Langlands.Algebra.NonUnitalModuleDualCompletion`, universe parameters `uA`, `uM`.

Worker 107 proves the unchanged Library proposition
`Langlands.Algebra.NonUnitalModuleDualCompletion.DualCompletionStatement.{uA, uM}`
(module `Langlands.Algebra.NonUnitalModuleDualCompletionStatement`). The exact-target theorem
is `Langlands.Algebra.NonUnitalModuleDualCompletion.dualCompletionStatement`. The module imports
only the statement module, which imports the published construction
`Langlands.Algebra.NonUnitalModuleDualCompletion`. Neither file is changed, and no hypothesis
is added.

## Source and route

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, I.4.3, printed p.25 /
PDF p.31. Worker 107 read this page. Renard writes that it is easy to see directly that
completing `M̃` recovers `M^*` ("Il est facile de voir directement que lorsqu'on complète `M̃`,
on retrouve `M^*`"). He then proves it formally through a chain of Hom isomorphisms, the
isomorphism `N_A ⊗_A M → N ⊗_A M` and A.III.3. This proof takes the direct route he mentions.
It evaluates both composites of the two published maps on vectors. It does not use the Hom
chain, the tensor smoothing isomorphism or Yoneda.

## Setting

`A : Type uA` is a `NonUnitalRing` with `Module ℂ A`, `IsScalarTower ℂ A A`,
`SMulCommClass ℂ A A` and `hA : IsIdempotented A`. `M : Type uM` is an additive group with an
original `NonUnitalModule A M` and `hM : IsNondegenerate A M`, so every `m` has an idempotent
`e` with `e · m = m`. All objects are the published ones from
`Langlands.Algebra.NonUnitalModuleDualCompletion` and its imports:

- `FullDual hA hM` is `M^* = Module.Dual ℂ M` for the canonical complex scalars on `M`, with
  the right action `(a · φ)(m) = φ(a · m)` (`NonUnitalModuleDual.fullAction`, written as a left
  `Aᵐᵒᵖ`-action);
- `Dual hA hM` is the nondegenerate part `M̃` of `M^*`;
- `NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)` is the completion of `M̃`: the families
  `x = (x(e))_e`, indexed by the idempotents `e` of `Aᵐᵒᵖ`, satisfying the fixation law
  `e · x(e) = x(e)` and the coherence law `e · x(f) = x(e)` for `e ≤ f`;
- `toCompletion hA hM φ` is the family whose `e`-coordinate is `e · φ`; its value at `m` is
  `φ(e.unop · m)` (`toCompletion_apply`);
- `toFullDual hA hM x` is the linear form whose value at `m` is
  `x(oppositeIdempotent e)(m)` for any idempotent `e` of `A` fixing `m`
  (`toFullDual_apply`).

## Implemented proof

**Private helper.** `unopIdempotent e` is the idempotent of `A` with value `e.unop`, for an
idempotent `e` of `Aᵐᵒᵖ`. Idempotence is `unop` applied to `e * e = e`. The lemma
`oppositeIdempotent_unopIdempotent` states `oppositeIdempotent (unopIdempotent e) = e` and is
proved by `rfl`, using `op (unop a) = a` and structure eta.

**First composite, `toFullDual_toCompletion`.** For `φ : FullDual hA hM`,
`toFullDual (toCompletion φ) = φ`. By `LinearMap.ext` it suffices to compare values at each
`m`. Choose `e` with `e · m = m` from `hM m`. `toFullDual_apply` with this `e` rewrites the
left side to the `oppositeIdempotent e` coordinate of `toCompletion φ` at `m`. By definition
this coordinate is `φ(e · m)`, stated by `change`. Rewriting with `e · m = m` gives `φ(m)`.

**Second composite, `toCompletion_toFullDual`.** For a compatible family `x`,
`toCompletion (toFullDual x) = x`. Two `Subtype.ext` steps, `funext` and `LinearMap.ext`
reduce this to: for each idempotent `e` of `Aᵐᵒᵖ` and each `m`,
`(toCompletion (toFullDual x))(e)(m) = x(e)(m)`. Write `e' = unopIdempotent e`. By definition
the left side is `toFullDual x (e' · m)`. Since `e'` is idempotent, it fixes `e' · m`
(`hfix`, by `mul_smul` and `e' * e' = e'`). So `toFullDual_apply` may be used with `e'` itself
as the fixing idempotent. With `oppositeIdempotent e' = e`, the left side becomes
`x(e)(e' · m)`. By the definition of the right action on `M̃`, this is `(e · x(e))(m)`,
stated by `change`. The fixation law `x.property.1 e : e · x(e) = x(e)` gives `x(e)(m)`.

This argument uses only the fixation law of `x`, not its coherence law. Taking `e'` as the
fixer of `e' · m` means no larger idempotent is needed. The statement Markdown's sketch instead
picks a larger fixer `f ≥ e` and uses coherence. Both routes give the same equality.

**Target theorem, `dualCompletionStatement`.** It introduces `A`, `M`, their instances, `hA`
and `hM`, and returns the pair `⟨toFullDual_toCompletion hA hM, toCompletion_toFullDual hA hM⟩`.
Its type is exactly `DualCompletionStatement.{uA, uM}`.

## Checks

A `lean_check` of the module gave 0 errors and 0 warnings. Inspection of
`dualCompletionStatement` reports the universe parameters `uA`, `uM` and only the axioms
`propext`, `Classical.choice` and `Quot.sound`. The file uses no `sorry`, `admit` or new
axioms. Its only option is `set_option autoImplicit false`.

## Scope

Together with the published `toCompletionHom` and `toFullDualHom` (both maps are
right-`A`-module maps) and `toCompletionLinear` and `toFullDualLinear` (both are
complex-linear), the two identities give the isomorphism `completion(M̃) ≃ M^*` of I.4.3.
This module proves only the two inverse identities. It does not package them as a bundled
equivalence.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Algebra.NonUnitalModuleDualCompletionStatement` | the target `DualCompletionStatement` and, through it, `toCompletion`, `toFullDual`, `toFullDual_apply`, `oppositeIdempotent`, `FullDual`, `Dual` and `NonUnitalModuleLeftLimit` |
