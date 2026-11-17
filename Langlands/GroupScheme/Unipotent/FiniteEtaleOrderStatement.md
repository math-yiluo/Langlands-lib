# Finite étale unipotent groups

`Langlands.GroupScheme.FiniteEtaleUnipotentOrderStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and `p : ℕ` with `[ExpChar k p]`. Let
`Ks : Type u` be a field with `[Algebra k Ks]` and `[IsSepClosure k Ks]`. Let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[IsFinite G.X.hom]` and
`[Etale G.X.hom]`. The proposition says

```text
IsUnipotent G ↔ ∃ n : ℕ, Nat.card (G.affinePoints (CommAlgCat.of k Ks)) = p ^ n
```

In words, a finite étale group scheme over `k` is unipotent exactly when its
order is a power of the characteristic exponent of `k`. The order is the
number of its `kˢ`-points.

The ingredients are existing declarations, used without change.

- `ExpChar k p` (Mathlib) says that `p` is the characteristic exponent of `k`.
  So `p = 1` if `k` has characteristic `0`, and otherwise `p` is the
  characteristic.
- `IsSepClosure k Ks` (Mathlib) says that `Ks` is a separable closure of `k`.
- `IsFinite G.X.hom` and `Etale G.X.hom` (Mathlib) say that the structure
  morphism `G.X.left ⟶ Spec k` is finite and étale.
- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector.
- `G.affinePoints (CommAlgCat.of k Ks)` (from
  [`AffinePoints`](../AffinePoints.md)) is the type of morphisms
  `Spec Ks ⟶ G.X` over `Spec k`, the `Ks`-points of `G`. `Nat.card` counts
  them. The type is finite because `G` is finite over `k`.

For `p = 1` the right-hand side says that `G` has exactly one `Ks`-point, so
the statement then says that the trivial group is the only finite étale
unipotent group in characteristic `0`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 14.14, p.283: "A finite étale algebraic group G is unipotent if
  and only if its order is a power of the characteristic exponent of k."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- 2.14 and 2.15, p.44: a finite algebraic group is one that "is finite as a
  scheme over k", and "The order of an étale group scheme G over k is the
  order of the abstract group G(k^s)."
- "Conventions and notation", p.3: "The characteristic exponent of k is p or
  1 according as its characteristic is p or 0", and `k^s` is the separable
  closure of `k` in an algebraic closure `k^a`.

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 14.14 on
printed p.283 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.3, 44 or 135.

Milne's proof reduces to `k` algebraically closed (14.9), where `G` is
constant. If `G` is not a `p`-group, it has a nontrivial subgroup of order
prime to `p`. By Maschke's theorem that subgroup has a nontrivial simple
representation, so it is not unipotent, and neither is `G` (14.7).
Conversely, a finite `p`-group in characteristic `p` has no nontrivial simple
representations (Milne cites Lang, *Algebra*, 2002, XVIII, Exercise 13). This
is explanation only. The statement does not depend on that route.

## Derivation from the source

- **Finite étale algebraic group.** Milne's finite étale algebraic group is a
  group scheme over `k` that is finite and étale as a `k`-scheme. The Lean
  hypotheses `IsFinite G.X.hom` and `Etale G.X.hom` say exactly this. A
  finite morphism is affine, which agrees with the Chapter 14 convention.
- **Unipotent.** Milne's definition is 6.45. `IsUnipotent G` uses only
  finite-dimensional representations, given by matrices after a choice of
  basis. This is the Library's predicate, and its comparison with 6.45 is
  recorded in [`Reductive.Basic`](../Reductive/Basic.md).
- **Order.** The order is the number of elements of `G(k^s)` (2.15). `G` is
  affine, so `G(k^s)` is the set of morphisms `Spec Ks ⟶ G.X` over `Spec k`,
  which is `G.affinePoints (CommAlgCat.of k Ks)`. The count does not depend on
  the choice of `Ks`, since any two separable closures of `k` are isomorphic
  over `k`.
- **Characteristic exponent.** Milne's characteristic exponent is Mathlib's
  `ExpChar k p`, and `p` is universally quantified with this instance.
  "A power of `p`" is `∃ n : ℕ, order = p ^ n`.
- **Universes.** One universe `u` is used for `k`, `Ks` and the schemes. This
  is a formalization convention.

## Related Library results

- `EtaleMultiplicativeTypeOrderStatement` (in
  [`Torus.EtaleMultiplicativeTypeOrderStatement`](../Torus/EtaleMultiplicativeTypeOrderStatement.md))
  is Milne's Example 12.28 with commutativity added: an étale group is of
  multiplicative type exactly when it is commutative and its order is prime
  to the characteristic exponent.
