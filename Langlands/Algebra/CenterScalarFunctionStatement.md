# The centre as an algebra of functions on the irreducibles (Renard I.1.8): statement

Module `Langlands.Algebra.CenterScalarFunctionStatement`.
Namespace `Langlands.Algebra`. Universe parameters `uA` (the algebra) and `uM` (module
carriers, enlarged to `max uA uM`).
The module contains one **statement**, the `Prop`-valued definition
`CenterScalarFunctionStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published modules around I.1.7–I.1.8 leave
I.1.8 open: [NondegenerateModuleCenter](NondegenerateModuleCenter.md) says
"Topology, closure, the unital-specialization comparison and I.1.8 remain separate
obligations". [NondegenerateModuleLinearActions](NondegenerateModuleLinearActions.md)
constructs the simultaneous action (I.1.8.2) and its extension to the completion, but no
assertion about them.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read I.1.8, printed pp.13–14 / PDF pp.19–20:

> Soit `A` une `ℂ`-algèbre à idempotents, de dimension finie ou dénombrable. Notons
> `Irr(A)` l'ensemble des classes d'isomorphie de modules simples dans `M(A)`. Le lemme de
> Schur B.II montre que tout élément `z` du centre `ℨ(A)` agit par un opérateur scalaire sur
> les modules simples. […] notons `z_M` ce scalaire. Il ne dépend évidemment que de la classe
> de `M` dans `Irr(A)`. […] Nous avons mis en évidence un morphisme d'algèbres :
> (I.1.8.1) `ℨ(A) → Fonc(Irr(A))`, `z ↦ [M ↦ z_M]`.
> […] (Sep) : pour tout `a ∈ A` non nul, il existe un module simple `M` non dégénéré et
> `m ∈ M` tels que `a · m ≠ 0`. De manière équivalente, […] le morphisme d'algèbres
> (I.1.8.2) `A → ∏_{M ∈ Irr(A)} End_ℂ(M)` est injectif.
> Le prolongement de (I.1.8.2) à `Â` reste injectif et il en est donc de même de sa
> restriction à `ℨ(A)`. Dans le cas où `A` vérifie la propriété (Sep), tout élément de
> `ℨ(A)` est donc caractérisé par la fonction sur `Irr(A)` qu'il définit.

## Published objects used

- `NondegenerateModuleCat.{uA, uM'} A` and its centre `NondegenerateModuleCenter.{uA, uM'} A`
  (Mathlib's `CatCenter`), as in the I.1.7 statements; `θ.app M` is the component at `M`.
- `NondegenerateScalars.scalarMul ℂ hM c m`: the canonical complex scalars on a
  nondegenerate module (I.2.1), `c · m = (c e) · m` for an idempotent `e` fixing `m`.
- `IdempotentedRingRightLimit A`: the completion `Â` (compatible right families), acting on
  nondegenerate modules by `IdempotentedRingRightLimitAction.act`, `x · m = x(e) · m` for an
  idempotent `e` fixing `m`. This is the extension of (I.1.8.2) to `Â`.
- `NonUnitalSubmodule A M`: the submodules (stable additive subgroups) of an original module.

## The statement

Let `A` be a complex algebra with idempotents: `NonUnitalRing A`, `Module ℂ A` with the
two compatibility classes `IsScalarTower ℂ A A` and `SMulCommClass ℂ A A`, and
`IsIdempotented A`. Assume `Module.rank ℂ A ≤ ℵ₀` ("de dimension finie ou dénombrable").
A nondegenerate module `M` is **simple** when it is nonzero and its only submodules are
`0` and `M`. Inside the statement, `acts z M m` is the action of `z ∈ ℨ(A)` on `m ∈ M`.
The statement asserts:

1. every `z ∈ ℨ(A)` acts on every simple `M` as multiplication by a unique complex scalar
   `c` for the canonical scalars. This is Renard's `z_M`;
2. if `M ≅ N` are simple, a scalar describing `z` on `M` also describes `z` on `N`, so `z_M`
   depends only on the class of `M`;
3. under (Sep), stated literally: every nonzero element of `Â` acts nontrivially on some
   simple module, and two elements of `ℨ(A)` that agree on every simple module are equal.

## Formalization choices

- **Irr(A) and Fonc(Irr(A)).** The statement does not form the set of isomorphism classes.
  Clauses 1–2 define `z_M` and show that it is constant on classes. The map (I.1.8.1) is
  then a function on classes. That it is a morphism of algebras follows from uniqueness in
  clause 1, since the operations of `ℨ(A)` are pointwise sums and compositions of
  components. This is not stated separately.
- **Injectivity.** The injectivity of (I.1.8.2) extended to `Â` is stated as: an element of
  `Â` acting by zero on all simple modules is zero. The injectivity of the restriction to
  `ℨ(A)` is stated as: elements of `ℨ(A)` agreeing on all simple modules are equal. Equal
  scalars on every simple module amount to equal actions there by clause 1.
- **Module universe.** Simple modules are quotients of `A`, so modules with carriers in a
  universe containing `A` suffice. The statement uses `max uA uM`, as do the I.1.7
  statements.
- **Simplicity.** Renard's "module simple dans `M(A)`" is a simple object of the category.
  For nondegenerate modules this is nontriviality plus the absence of proper nonzero
  submodules, since submodules of nondegenerate modules are nondegenerate. The published B.II
  statements (`NonUnitalSchurStatements`) use the same formulation.

## Why the statement is true

1. `θ_M` is an additive endomorphism of `M` commuting with `A`. `M` is simple and `A` has
   countable dimension, so by Schur's lemma B.II (published `NonUnitalSchurStatements`)
   `θ_M` is a canonical scalar. Uniqueness holds because `M` is nonzero.
2. Naturality of `θ` with respect to an isomorphism `f : M → N`, together with
   `f(c · m) = c · f(m)` for the canonical scalars (intertwiners are automatically
   complex-linear, I.2.1).
3. Let `x ∈ Â` act by zero on every simple module. If `x(e) ≠ 0` for some `e`, (Sep) gives
   a simple `M` and `m` with `x(e) · m ≠ 0`. Put `m' = e · m`. Then `e` fixes `m'` and
   `x · m' = x(e) · m' = x(e) · m ≠ 0`, a contradiction. Hence `x = 0`. For `ℨ(A)`, the
   I.1.7 identification (the published statement
   `NondegenerateModuleCenterTheoremStatement`, under review) writes `θ` and `θ'` as the
   actions of elements of the commutant of `A` in `Â`, and their difference then acts by
   zero on all simple modules.

## Remaining obligations

The proof is a separate obligation. It needs B.II (`NonUnitalSchurStatements`), the I.2.1
scalars, and, for the last assertion, the I.1.7 identification of the centre.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Algebra.NondegenerateModuleCenter` | `NondegenerateModuleCenter`, `NondegenerateModuleCat`, `IdempotentedRingRightLimit`, `IdempotentedRingRightLimitAction.act` (through its imports) |
| `Langlands.Algebra.NondegenerateScalars` | `NondegenerateScalars.scalarMul` |
| `Mathlib.LinearAlgebra.Dimension.Basic` | `Module.rank` |
