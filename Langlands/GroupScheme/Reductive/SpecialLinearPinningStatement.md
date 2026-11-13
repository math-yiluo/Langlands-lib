# A simply connected pinning of type `A_n` of the special linear group: statement

This module defines the proposition
`Langlands.GroupScheme.SpecialLinearSimplyConnectedPinningStatement` (universe
parameter `u`). It is a statement only. The module supplies no proof. It is a
prerequisite of Task 5703 (simply connected groups of inner type `A_n` as
reduced-norm-one groups), where it identifies the split model of an inner form of type
`A_n` with `SL_{n+1}`.

## Statement

For every field `k : Type u` and every natural number `n`, the actual special linear
group scheme `SL_{n+1}` over `Spec k` (`SpecialLinear.groupScheme (Fin (n + 1))
(CommRingCat.of k)`, the determinant-one functor) has a split pinning `p : SplitPinning
SL_{n+1}` with two properties:

1. **Simply connected.** The coroots of the root datum `p.rootDatum` span the whole
   cocharacter lattice over `ℤ`: `p.rootDatum.corootSpan ℤ = ⊤`.
2. **Type `A_n`.** Some bijection `e : p.base.support ≃ Fin n` between the simple roots
   of the pinning's base and `Fin n` satisfies `p.rootDatum.pairing a b =
   CartanMatrix.A n (e a) (e b)` for all simple roots `a`, `b`. So the simple pairings
   form Mathlib's Cartan matrix of type `A_n`.

The `IsAffineHom` instance that `SplitPinning` needs for `SL_{n+1}` is supplied inside
the statement by `SpecialLinear.isAffineHom_groupScheme`.

`SplitPinning` is the Library's notion of a pinning: a split maximal torus, its actual
root datum (roots, coroots and reflections from the normalizer), a base, and nonzero
simple-root vectors in the Lie algebra. The statement therefore concerns the actual
root datum of `SL_{n+1}`, not an abstract one.

For `n = 0` the group `SL_1` is trivial. The torus is trivial, the cocharacter lattice
is zero, the base is empty and `Fin 0` is empty, so both conditions hold trivially.

## Provenance

This is the classical description of `SL_{n+1}` as the simply connected split
almost-simple group of type `A_n`.

- Milne, *Algebraic groups* (2017), Example 23.61, printed p.502 (PDF p.518): "The
  groups SL_n, Sp_2n, and Spin_n are simply connected".
- Milne (2017), §24.c, printed p.517 (PDF p.533): "the simply connected split
  almost-simple group of type A_n is SL_{n+1}".

The Lean formulation is derived. "Simply connected" is expressed by the criterion that
the coroots span the cocharacter lattice. For split semisimple groups the Library proves
this criterion equivalent to the scheme-theoretic definition (`splitCorootSpanSimplyConnected`
and `splitSimplyConnectedCorootSpan`). "Type `A_n`" is expressed by the simple
pairings `p.rootDatum.pairing a b = ⟨α_a, α_b^∨⟩`, numbered so that they give
`CartanMatrix.A n` (a symmetric matrix, so the order of the pairing does not matter). With the
standard diagonal torus and the base `ε_i - ε_{i+1}`, this is the familiar tridiagonal
Cartan matrix.
