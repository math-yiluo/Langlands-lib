# Statement: subgroups containing a Borel subgroup are connected and self-normalizing

Worker 75.

`Langlands.GroupScheme.BorelContainingSubgroupSelfNormalizerStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsGeometricBorelSubgroup` and,
  through its imports, `IsBorelSubgroup`, `IsClosedSubgroup` and the group-scheme vocabulary
  over a field.
- [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md), for
  `SubgroupFunctor.normalizer`.

## Lean statement

```lean
def BorelContainingSubgroupSelfNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (P B : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G) (j : B ⟶ G) (f : B ⟶ P),
    IsClosedSubgroup i → Smooth P.X.hom → IsGeometricBorelSubgroup j → f ≫ i = j →
      ConnectedSpace P.X.left ∧
        (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsClosedSubgroup i` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `i` is a closed immersion.
- `IsBorelSubgroup j` ([`Absolute.Borel`](Borel.md)): `j` is a closed immersion, `B` is smooth,
  connected and solvable, and `j` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- `IsGeometricBorelSubgroup j` ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)):
  `IsBorelSubgroup j` holds, and so does `IsBorelSubgroup` of the base change of `j` to an
  algebraic closure of `k`.
- `SubgroupFunctor.range i`: the points of `G` that factor through `i`, on every scheme over
  `Spec k`.
- `F.normalizer` ([`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md)): a point `g`
  over `U` lies in it when, after every base change `a : V ⟶ U`, conjugation by `a ≫ g` and by
  its inverse maps `F(V)` into itself.

## Statement and quantifiers

Let `k : Type u` be a field and `G` a smooth, affine, connected group scheme over `Spec k`.
Let `i : P ⟶ G` be a smooth closed subgroup and `j : B ⟶ G` a geometric Borel subgroup that
factors through `i` (`f ≫ i = j`). Then `P` is connected, and the normalizer of `P` in `G`
equals `P`, as subgroup functors of `G` on all schemes over `Spec k`: `N_G(P) = P`.

Taking `P = B`, `i = j` and `f = 𝟙 B` gives Milne's normalizer theorem `N_G(B) = B`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Theorem 17.48 (normalizer theorem), p.367: "Let B be a Borel subgroup of G. Then
  B = N_G(B)."
- Corollary 17.49, p.367: "Let P be a subgroup variety of G. If P contains a Borel subgroup of
  G, then P is connected and P = N_G(P)."
- Section 17e, opening, p.366: "Throughout, G is a connected group variety over a field k (not
  necessarily algebraically closed field)." Section 17d, opening, p.363: "An algebraic
  subgroup of a connected group variety G over k is Borel if it becomes Borel over k^a."
- Definition 17.6, p.353: over an algebraically closed field a Borel subgroup is a maximal
  connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field. Definition
  1.3, p.7: a subgroup variety is an algebraic subgroup whose underlying scheme is a variety;
  remark after 1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns Theorem
17.48 or Corollary 17.49.

Milne's proof of 17.49: reduce to `k` algebraically closed. `P` contains a Cartan subgroup, so
`N_G(P)` is smooth (17.47), and it suffices to show `P°(k) = N_G(P)(k)`. For
`x ∈ N_G(P)(k)`, `B` and `xBx⁻¹` are Borel subgroups of `P°`, so `pxB(px)⁻¹ = B` for some
`p ∈ P°(k)`; by 17.48, `px ∈ B(k)`, so `x ∈ P°(k)`. This is explanation only.

## Derivation from the source

- **Connected group variety over any field.** `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`,
  `[ConnectedSpace G.X.left]`, with no hypothesis on `k`, as in Section 17e.
- **Subgroup variety `P`.** A closed subgroup `i` with `P` smooth.
- **Borel subgroups over `k`.** Milne's Section 17d convention, a subgroup that becomes Borel
  over `k^a`, is `IsGeometricBorelSubgroup j`.
- **"`P` contains `B`".** Encoded by a factorization `f : B ⟶ P` with `f ≫ i = j`.
- **`N_G(P)`.** Milne's normalizer is the functor of `R`-points `g` with `g P_R g⁻¹ = P_R`,
  represented by a closed subgroup. The Library's `normalizer` is the all-test version on
  schemes over `Spec k`, and `P = N_G(P)` is equality of subgroup functors of `G`. This is the
  scheme-theoretic equality that Milne proves, not only an equality of groups of `k`-points.
- **Both results in one statement.** Corollary 17.49 contains Theorem 17.48 as the case
  `P = B`, so one statement records both.

## Related Library results

- [`Absolute.BorelContainingSubgroupConnectedStatement`](BorelContainingSubgroupConnectedStatement.md)
  states the connectedness part over an algebraically closed field.
- `BorelNormalizerStatement` in [`Absolute.BorelStatement`](BorelStatement.md) states the
  normalizer theorem over an algebraically closed field for the group of `k`-points.
- `ParabolicSelfNormalizerStatement` in
  [`Rational.ParabolicNormalizerStatement`](../Rational/ParabolicNormalizerStatement.md) states
  the self-normalizing property of parabolic subgroups of connected reductive groups over any
  field.
