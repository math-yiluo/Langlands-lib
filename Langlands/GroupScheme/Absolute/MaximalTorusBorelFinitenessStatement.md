# Statement: a maximal torus lies in finitely many Borel subgroups

Worker 75.

`Langlands.GroupScheme.MaximalTorusBorelFinitenessStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup`,
`IsMaximalTorus` and the group-scheme vocabulary over a field.

## Lean statement

```lean
def MaximalTorusBorelFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
      Set.Finite {F : SubgroupFunctor G |
        ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
          IsBorelSubgroup i ∧ SubgroupFunctor.range i = F ∧ SubgroupFunctor.range j ≤ F}
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `T.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsMaximalTorus j` ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a torus, `j` is a closed
  immersion, and `j` does not factor through a strictly larger closed torus of `G`.
- `IsBorelSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed immersion, `B` is smooth,
  connected and solvable, and `i` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- `SubgroupFunctor G` is the type of subgroup functors of `G` on schemes over `Spec k`, ordered
  by inclusion of points; `SubgroupFunctor.range i` is the subfunctor of points factoring
  through `i`.
- `Set.Finite`: Mathlib's finiteness of a set.

## Statement and quantifiers

For every algebraically closed field `k : Type u`, every smooth, affine, connected group scheme
`G` over `Spec k` and every maximal torus `j : T.toGrp ⟶ G`: the set of subgroup functors of
`G` of the form `SubgroupFunctor.range i`, for a Borel subgroup `i : B ⟶ G` whose range
contains the range of `j`, is finite.

Borel subgroups are counted as subgroups of `G`, through their ranges: a closed immersion is
determined up to unique isomorphism over `G` by its range, so different representatives of one
Borel subgroup give the same element of the set.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 17.26, p.360: "(a) A maximal torus of G is contained in only finitely many Borel
  subgroups. (b) For a Borel subgroup B of G, B = N_G(B)°_red."
- Section 17b, opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k."
- Definition 17.6, p.353: a Borel subgroup is a maximal connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; p.13:
  "group variety" = "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. The p.360 entry corrects the remark before 17.28 ("SL₂ (not SL₃) has dimension
3"); it does not concern Corollary 17.26.

Milne's proof of (a): the Borel subgroups containing `T` are permuted transitively by
`N_G(T)(k)` (17.11), and `N_G(T)°` lies in each of them (via 13.10, 12.38 and 17.23), so their
number is at most `(N_G(T)(k) : N_G(T)°(k)) < ∞`. This is explanation only.

## Derivation from the source

- **Connected group variety.** As in Section 17b: `[IsAlgClosed k]`, `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **Contained in.** "`T` is contained in `B`" is inclusion of subgroups of `G`, encoded by
  `SubgroupFunctor.range j ≤ SubgroupFunctor.range i`.
- **Finitely many Borel subgroups.** The Borel subgroups are collected as subgroups of `G`
  (subgroup functors), as explained above, and the set is required to be finite.

## Scope

- Part (b) of the corollary is not stated. It is a consequence of the normalizer theorem
  `N_G(B) = B` (Milne, Theorem 17.48), whose statement on `k`-points the Library records as
  `BorelNormalizerStatement` in [`Absolute.BorelStatement`](BorelStatement.md).

## Related Library results

- [`Absolute.BorelStatement`](BorelStatement.md) states conjugacy of Borel subgroups (17.9(b))
  and of maximal tori (17.10).
- [`Absolute.BorelMaximalTorusStatement`](BorelMaximalTorusStatement.md) states that every Borel
  subgroup contains a maximal torus.
