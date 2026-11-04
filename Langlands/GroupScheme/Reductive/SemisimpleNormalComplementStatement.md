# Commuting normal complements in semisimple groups

Worker 1522.

This module defines one structural proposition and proves nothing.
`Langlands.GroupScheme.SemisimpleNormalComplementStatement.{u}` is the
normal-subgroup part of Milne's structure theorem for semisimple groups
(Theorem 21.51), specialized to algebraically closed fields. It is stated in
the weak form used by
`Adjoint/NormalEquivariantRetractionReduction.lean`.

## Statement

For every field `k : Type u` with `IsAlgClosed k` and actual group schemes `G`
and `H` over `Spec k`, assume:

- `IsSemisimple G`;
- `j : H ⟶ G` is a group-scheme homomorphism with `IsClosedSubgroup j`, that
  is, `j.hom.hom.left` is a closed immersion;
- `Smooth H.X.hom` and `ConnectedSpace H.X.left`;
- `(SubgroupFunctor.range j).IsNormal`: the all-test image functor of `j` is
  normalized by every point of `G` over every scheme over `Spec k`.

Then the statement asserts that there are an actual group scheme `K` over
`Spec k` and a homomorphism `i : K ⟶ G` with:

1. `IsClosedSubgroup i`;
2. `(SubgroupFunctor.range i).IsNormal`;
3. for every scheme `T` over `Spec k` and all points `x : T ⟶ H.X` and
   `y : T ⟶ K.X`, the points `x ≫ j.hom.hom` and `y ≫ i.hom.hom` of `G`
   commute;
4. `Flat (subgroupMultiplication j i).left` and
   `Surjective (subgroupMultiplication j i).left`.

Here `subgroupMultiplication j i : H.X ⊗ K.X ⟶ G.X` is the published morphism
of `Rational/LeviSubgroup.lean`. It is the product, in the group of points
`H.X ⊗ K.X ⟶ G.X`, of the two projections followed by `j` and `i`; on points
it is `(x, y) ↦ j(x) i(y)`. The source `H.X ⊗ K.X` is the fibre product over
`Spec k`. Thus item 4 says that the multiplication morphism of schemes
`H ×_k K → G` is faithfully flat. By item 3 it is a group homomorphism from
the product group, although the statement does not package it as one.

## Source

J. S. Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

- Theorem 21.51, printed pp. 440–441 (PDF pp. 456–457): "A semisimple
  algebraic group `G` has only finitely many almost-simple normal subgroup
  varieties `G_1, …, G_r` and is the almost-direct product of them. Every
  connected normal subgroup variety of `G` is a product of those `G_i` that it
  contains, and is centralized by the remaining ones."
- 2.31, printed p. 49 (PDF p. 65): `G` is the almost-direct product of
  algebraic subgroups `G_1, …, G_n` if the multiplication map
  `G_1 × ⋯ × G_n → G` is a faithfully flat homomorphism with finite kernel.
  Then the `G_i` commute in pairs and are normal.
- Proposition 1.70, printed p. 28 (PDF p. 44): a surjective homomorphism onto a
  reduced algebraic group is faithfully flat. Theorem 1.72 and
  Definition 1.73, printed p. 29 (PDF p. 45): the image of a homomorphism from
  a smooth algebraic group is an algebraic subgroup, onto which the
  homomorphism is faithfully flat.

## Derivation from the source

Write `N` for the image of `j`. Milne's "subgroup variety" is a smooth
algebraic subgroup. Over the algebraically closed field `k`, `N` is therefore a
connected normal subgroup variety of `G`. By Theorem 21.51, `N` is the product
of the almost-simple factors `G_i`, `i ∈ I`, that it contains, and `N` is
centralized by the remaining factors. Take `K` to be the product of the
remaining factors `G_i`, `i ∉ I`, meaning the image of their multiplication map
(1.72, 1.73), with `i` its inclusion. Then:

- `K` is an algebraic subgroup, so `i` is a closed immersion;
- `K` is normal, because each `G_i` is normal (2.31);
- `N` and `K` commute, because `N` is centralized by every `G_i` with
  `i ∉ I`;
- `G_1 × ⋯ × G_r → G` is surjective and factors through the multiplication
  `N × K → G`. Hence the latter is surjective, and since `G` is smooth it is
  faithfully flat (1.70).

The statement omits the rest of Theorem 21.51 and of the almost-direct
product: finiteness of the kernel of `N × K → G`, smoothness and connectedness
of `K`, and the decomposition into almost-simple factors. It does not require
uniqueness of `K`.

## Conventions and comparison

- `IsSemisimple G` is the published predicate of `Reductive/Semisimple.lean`:
  connected reductive with finite scheme-theoretic centre. As explained in
  `Reductive/Semisimple.md`, Milne's Proposition 19.10 characterizes semisimple
  groups among reductive groups by finiteness of the centre.
- Milne states normality and centralization for functors on `k`-algebras. The
  Lean statement requires them, as conclusions, on every scheme over `Spec k`.
  Points of `G` form a Zariski sheaf, and the closed subgroups `N` and `K`
  represent Zariski subsheaves. Hence normality and commutation on affine tests
  imply them on all tests, by gluing along an affine open cover. This
  comparison is part of the obligation of a proof and is not proved here.
- Milne's theorem holds over any field. The specialization to algebraically
  closed fields suffices for the intended use, whose target statement also
  assumes `IsAlgClosed k`.

## Use

`Adjoint/NormalEquivariantRetractionReduction.lean` proves that this statement
implies `NormalAdjointEquivariantRetractionStatement`
(`Adjoint/NormalEquivariantRetractionStatement.lean`). There, a trivial centre
of `H` makes the multiplication a monomorphism, so it is an isomorphism.
Accepting this statement does not prove it. In particular, its proof needs the
root-theoretic structure theory of split reductive groups used in Milne's proof
of Theorem 21.51.
