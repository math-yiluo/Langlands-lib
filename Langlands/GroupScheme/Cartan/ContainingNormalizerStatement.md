# Statement: normalizers of subgroups containing a Cartan subgroup

Worker 75.

`Langlands.GroupScheme.CartanContainingNormalizerStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Cartan.Basic`](Basic.md), for `IsCartanSubgroup` and, through its imports, the
  group-scheme vocabulary over a field.
- [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md), for
  `SubgroupFunctor.normalizer`.

## Lean statement

```lean
def CartanContainingNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
    IsClosedSubgroup h → Smooth H.X.hom →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G), IsCartanSubgroup c →
      SubgroupFunctor.range c ≤ SubgroupFunctor.range h →
    ∀ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
      (SubgroupFunctor.range h).normalizer.IsRepresentedBy n → IsClosedSubgroup n →
        Smooth N.X.hom ∧ ∀ f : H ⟶ N, f ≫ n = h → IsOpenImmersion f.hom.hom.left
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`; `G.X.left` is the underlying scheme and `G.X.hom` its structure morphism.
  For a homomorphism `f : H ⟶ N`, `f.hom.hom.left` is its underlying morphism of schemes.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`, `IsOpenImmersion`: as in Mathlib.
- `IsClosedSubgroup f` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `f` is a closed immersion.
- `IsCartanSubgroup c` ([`Cartan.Basic`](Basic.md)): `c` is a closed immersion and
  `SubgroupFunctor.range c = torusCentralizer j` for some maximal torus `j : T ⟶ G`
  (`IsMaximalTorus j`, [`Torus.Maximal`](../Torus/Maximal.md): `T` is a torus, `j` is a closed
  immersion, and `j` does not factor through a strictly larger closed torus of `G` over `k`).
- `SubgroupFunctor.range f`: the points of `G` that factor through `f`; subgroup functors are
  ordered by inclusion of points.
- `F.normalizer` ([`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md)): a point `g`
  over `U` lies in it when, after every base change `a : V ⟶ U`, conjugation by `a ≫ g` and by
  its inverse maps `F(V)` into itself.
- `F.IsRepresentedBy n` ([`SubgroupFunctor`](../SubgroupFunctor.md)): `n` is a monomorphism and
  `SubgroupFunctor.range n = F`.

## Statement and quantifiers

Let `k : Type u` be a field and `G` a smooth, affine, connected group scheme over `Spec k`. Let
`h : H ⟶ G` be a smooth closed subgroup containing a Cartan subgroup `c : C ⟶ G`. Let
`n : N ⟶ G` be any closed subgroup representing the normalizer `N_G(H)`. Then `N` is smooth,
and the factorization `f : H ⟶ N` of `h` through `n` is an open immersion. (Such an `f` exists
and is unique, since `H ⊆ N_G(H)` and `n` is a monomorphism; the statement quantifies over it
to avoid choosing it.)

**Why "`H` open in `N`" is Milne's `N_G(H)° = H°`.** The factorization `f` is a closed
immersion, because `f ≫ n = h` is one and `n` is separated. If `f` is also an open immersion,
`H` is an open and closed subgroup scheme of `N`, so it contains the identity component `N°`
as an open subscheme and `H° = N°`. Conversely, if `H° = N°` then `H` is a union of cosets of
the open subgroup `N°`, so `f` is an open immersion. The smoothness of `N` is Milne's
parenthetical consequence; it is kept as a separate conjunct.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Lemma 17.47, p.366: "Let H be a subgroup variety of G. If H contains a Cartan subgroup of G,
  then N_G(H)° = H° (and so N_G(H) is smooth)."
- Section 17e, opening, p.366: "Throughout, G is a connected group variety over a field k (not
  necessarily algebraically closed field)."
- Definition 17.43, p.364: a Cartan subgroup is the centralizer of a maximal torus. Section
  17d, opening, p.363: over a general field a maximal torus is a torus `T` with `T_{k^a}`
  maximal in `G_{k^a}`; "Later (17.82) we shall see that this agrees with the obvious
  definition."
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field. Definition
  1.3, p.7: "An algebraic subgroup is called a subgroup variety if its underlying scheme is a
  variety"; remark after 1.26, p.13: "group variety" means "smooth algebraic group". So a
  subgroup variety is a smooth algebraic subgroup.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns Lemma
17.47.

Milne's proof: reduce to `k` algebraically closed. With `N = N_G(H)`,
`dim h = dim H ≤ dim N ≤ dim n`, and `n/h = (g/h)^H` (10.34). As `H ⊇ C = C_G(T)`,
`h ⊇ c = g^T`; since `T` is linearly reductive, `(g/h)^T = 0`, so `n = h`, and `N` is smooth
with `N° = H°`. This is explanation only.

## Derivation from the source

- **Connected group variety over any field.** `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`,
  `[ConnectedSpace G.X.left]`, with no hypothesis on `k`, as in Section 17e.
- **Subgroup variety `H`.** A closed subgroup `h` with `H` smooth.
- **Cartan subgroups over `k`.** `IsCartanSubgroup c` uses maximality of the torus over `k`.
  This agrees with Milne's Section 17d convention (maximality over `k^a`): the Library proves
  that a closed torus is maximal over `k` exactly when its base change to any field extension
  is maximal (`maximalTorusBaseChange`, [`Torus.MaximalBaseChangeProof`](../Torus/MaximalBaseChangeProof.md);
  this is Milne's 17.82).
- **"Contains".** `range c ≤ range h`, an inclusion of subgroup functors of `G`.
- **`N_G(H)`.** Milne's normalizer is the functor of `R`-points `g` with `g H_R g⁻¹ = H_R`,
  represented by a closed subgroup. The Library's `normalizer` is the all-test version on
  schemes over `Spec k`; the statement quantifies over every closed subgroup representing it.
- **`N_G(H)° = H°`.** Encoded as "the factorization of `h` through `n` is an open immersion",
  as explained above, since the Library has no identity-component construction for arbitrary
  closed subgroups.

## Related Library results

- [`Cartan.StructureStatement`](StructureStatement.md): every Cartan subgroup is smooth,
  connected and nilpotent (proved in [`Cartan.StructureProof`](StructureProof.md)).
- [`Torus.MaximalBaseChangeProof`](../Torus/MaximalBaseChangeProof.md): maximality of a closed
  torus is invariant under field extension.
