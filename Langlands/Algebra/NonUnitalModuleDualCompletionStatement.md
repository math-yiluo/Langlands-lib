# The completion of the nondegenerate dual is the full dual (Renard I.4.3): statement

Module `Langlands.Algebra.NonUnitalModuleDualCompletionStatement`.
Namespace `Langlands.Algebra.NonUnitalModuleDualCompletion`. Universe parameters `uA`, `uM`.
The module contains one **statement**, the `Prop`-valued definition
`DualCompletionStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published construction
[NonUnitalModuleDualCompletion](NonUnitalModuleDualCompletion.md) writes down both maps
between `M^*` and the completion of `M̃` and proves their intrinsic laws, and says: "Nor is
it proved that the two maps are inverse to each other." This unit states that assertion,
which is the conclusion of I.4.3.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read I.4.3, printed p.25 / PDF p.31:

> Soit `A` une `ℂ`-algèbre à idempotents et soit `M` un `A`-module non dégénéré. On a défini
> `M̃` comme la partie non dégénérée de `M^*`. Il est facile de voir directement que
> lorsqu'on complète `M̃`, on retrouve `M^*`. Nous allons donner une démonstration de ce
> fait qui découle formellement de ce qui a déjà été établi. […] On en déduit d'après A.III.3
> que `\widehat{M̃} = \widehat{(M^*)_A} ≃ M^*`.

In the printed display both left-hand terms carry the completion hat: the completion of `M̃`
equals the completion of `(M^*)_A`, and this is isomorphic to `M^*`. Here `(M^*)_A` is the
nondegenerate part of `M^*`, which is `M̃` itself, not its completion, and in general it is
not isomorphic to `M^*` as an `A`-module. For `A = ⊕_{n ∈ ℕ} ℂ` with coordinatewise multiplication and `M = A`, `M^*` is
the space of all sequences, while `(M^*)_A` is the space of finitely supported sequences.
The completion of a nondegenerate module is the module of compatible families of I.1.4.

## Published objects used

From `Langlands.Algebra.NonUnitalModuleDualCompletion` and its imports:

- `FullDual hA hM`: the full complex dual `M^* = Module.Dual ℂ M`, for the canonical complex
  scalars on the nondegenerate module `M` (I.2.1), with the right `A`-action
  `(a · φ)(m) = φ(a · m)` (`NonUnitalModuleDual.fullAction`);
- `Dual hA hM`: the nondegenerate part `M̃` of `M^*` (`NonUnitalModuleDual.dualAction`);
- `NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)`: the completion of `M̃` (I.1.4), the
  compatible families of vectors of `M̃` indexed by the idempotents of `Aᵐᵒᵖ`;
- `toCompletion hA hM`: `φ ↦ (e · φ)_e`;
- `toFullDual hA hM`: a family `x` goes to the linear form `m ↦ x(e)(m)` for any idempotent
  `e` fixing `m`.

The published `toCompletionHom` and `toFullDualHom` show that both maps are `A`-module
maps. `toCompletionLinear` and `toFullDualLinear` show that they are complex-linear.

## The statement

For every complex algebra with idempotents `A` (`NonUnitalRing A`, `Module ℂ A`,
`IsScalarTower ℂ A A`, `SMulCommClass ℂ A A`, `IsIdempotented A`) and every nondegenerate
original `A`-module `M`:

1. `toFullDual (toCompletion φ) = φ` for every `φ ∈ M^*`;
2. `toCompletion (toFullDual x) = x` for every compatible family `x`.

Together with the published module-map laws, this is the isomorphism of right `A`-modules
`completion(M̃) ≃ M^*` of I.4.3.

## Formalization choices

- **Direct route.** Renard proves the assertion by a chain of natural Hom isomorphisms,
  the isomorphism `ι : N_A ⊗_A M → N ⊗_A M` and Yoneda (A.III.3). The published
  `NonUnitalTensorSmoothingStatements` states, and `NonUnitalTensorSmoothingProof` proves,
  that `ι` is an isomorphism. The statement asserts only the conclusion, in the explicit
  form that his opening sentence calls easy to see directly. A proof may follow either route.
- **Right modules.** Right `A`-modules are left `Aᵐᵒᵖ`-modules, as in the published dual.

## Why the statement is true

1. Take `e` fixing `m`. Then `toFullDual (toCompletion φ) m = (e · φ)(m) = φ(e · m) = φ(m)`.
2. The `e`-coordinate of `toCompletion (toFullDual x)` is `e · toFullDual x`. On `m`, choose
   `f` fixing `e · m` with `e ≤ f`. Its value is `x(f)(e · m)`, which equals `x(e)(m)` by
   coherence of `x`.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Algebra.NonUnitalModuleDualCompletion` | `toCompletion`, `toFullDual`, `FullDual`, `Dual`, `NonUnitalModuleLeftLimit` and the dual actions |
