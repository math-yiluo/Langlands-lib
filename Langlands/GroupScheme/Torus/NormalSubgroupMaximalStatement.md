# Statement: maximal tori of a normal subgroup variety

`Langlands.GroupScheme.NormalSubgroupMaximalTorusStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Torus.Maximal`](Maximal.md), for `IsMaximalTorus` and,
through its imports, `IsClosedSubgroup`, `SubgroupFunctor` and the group-scheme vocabulary over
a field.

## Lean statement

```lean
def NormalSubgroupMaximalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
    IsClosedSubgroup n → Smooth N.X.hom → (SubgroupFunctor.range n).IsNormal →
      (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
        ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ N),
          IsMaximalTorus s ∧ SubgroupFunctor.range (s ≫ n) ≤ SubgroupFunctor.range j) ∧
      (∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ N), IsMaximalTorus s →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsMaximalTorus j ∧ SubgroupFunctor.range (s ≫ n) ≤ SubgroupFunctor.range j)
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` the commutative
  group schemes; `T.toGrp` is the underlying group scheme of `T`. For `G : GroupScheme S`,
  `G.X` is its scheme over `S`, `G.X.left` the underlying scheme and `G.X.hom` the structure
  morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsClosedSubgroup n`: the morphism of schemes underlying `n` is a closed immersion.
- `SubgroupFunctor.range n`: the points of `G` that factor through `n`, on every scheme over
  `Spec k`. `F.IsNormal` (`SubgroupFunctor`) says that for every scheme `T` over `Spec k`, every
  point `g` of `G` over `T` and every `x ∈ F(T)`, `g x g⁻¹ ∈ F(T)`.
- `IsMaximalTorus j` ([`Torus.Maximal`](Maximal.md)): `T` is a torus, `j` is a closed
  immersion, and `j` does not factor through a strictly larger torus that is a closed subgroup.
  It applies to `s : S.toGrp ⟶ N` with `N` as the ambient group.
- For closed subgroups, `SubgroupFunctor.range (s ≫ n) ≤ SubgroupFunctor.range j` says that
  `S`, viewed in `G` through `n`, is contained in `T`.

## Statement and quantifiers

For every field `k : Type u`, every smooth, affine, connected group scheme `G` over `Spec k`
and every smooth closed normal subgroup `n : N ⟶ G`:

1. for every maximal torus `j : T ⟶ G` there is a maximal torus `s : S ⟶ N` of `N` with
   `S ⊆ T`;
2. for every maximal torus `s : S ⟶ N` of `N` there is a maximal torus `j : T ⟶ G` of `G`
   with `S ⊆ T`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 17.85, p.379: "Let G be a connected group variety and N a normal subgroup variety.
  If T is a maximal torus in G, then (T ∩ N)_t is a maximal torus in N, and every maximal torus
  in N is of this form." It is in Section 17j, "Maximal tori and Cartan subgroups over an
  arbitrary base field", and the base field `k` is arbitrary.
- Notation 12.29, p.241, recalled just before 17.85: for an algebraic group `H` of
  multiplicative type, `H_t` "is the largest subtorus of H".
- Section 17d, p.363: over an arbitrary field, a maximal torus of `G` is a torus `T` with
  `T_{k^a}` maximal in `G_{k^a}`; by Theorem 17.82, p.379, this agrees with the obvious
  definition for a group variety.
- Definition 1.51(a), p.21: "An algebraic subgroup H of G is normal if H(R) is normal in G(R)
  for all small k-algebras R." Definition 1.3, p.7: "An algebraic subgroup is called a
  subgroup variety if its underlying scheme is a variety"; remark after 1.26, p.13: "group
  variety" means "smooth algebraic group". So a subgroup variety is a smooth algebraic
  subgroup. Algebraic subgroups are closed (Proposition 1.41, p.18).
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) has, for Chapter 1, a note on the placement
of Notation 3.2 and corrections on pp.18, 20, 21 (Definition 1.48) and 26; for Chapter 12,
corrections to 12.41 and 12.57; and for Chapter 17, corrections only on pp.360, 364 and 386.
None concerns Definitions 1.3 or 1.51, Notation 12.29 or Corollary 17.85.

Milne's proof (p.380): let `T'` be a maximal torus of `N` and `T''` a maximal torus of `G`
containing `T'`. Then `T''_{k^a}` is maximal in `G_{k^a}` (17.82), so `T_{k^a} = g T''_{k^a} g⁻¹`
for some `g ∈ G(k^a)` (17.10), and `((T ∩ N)_t)_{k^a} = (T_{k^a} ∩ N_{k^a})_t =
g (T''_{k^a} ∩ N_{k^a})_t g⁻¹ = g T'_{k^a} g⁻¹`, which is maximal in `N_{k^a}`. So `(T ∩ N)_t` is
maximal in `N`. For the second part, `T' = (T'' ∩ N)_t`. This is explanation only.

## Derivation from the source

- **Connected group variety; normal subgroup variety.** `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]` (Chapter 17 convention) and `[ConnectedSpace G.X.left]`; `n` a closed
  immersion with `N` smooth. Normality is `(SubgroupFunctor.range n).IsNormal`, on all schemes
  over `Spec k`. Milne's condition is the case of affine test schemes `Spec R`; it implies
  the general case, because whether a point of `G` over `T` factors through the closed
  immersion `n` can be checked on an affine open cover of `T`.
- **Maximal tori.** `IsMaximalTorus`, the obvious definition. By Theorem 17.82 it agrees with
  Milne's definition on p.363, both for `G` and for the group variety `N` (17.82 does not
  assume connectedness).
- **"(T ∩ N)_t is a maximal torus in N".** This is part 1. If `(T ∩ N)_t` is maximal in `N`,
  it is a maximal torus of `N` contained in `T`. Conversely, if `S` is a maximal torus of `N`
  contained in `T`, then `S ⊆ T ∩ N`, so `S ⊆ (T ∩ N)_t` (the largest subtorus, 12.29). Since
  `(T ∩ N)_t` is a torus of `N`, maximality of `S` gives `S = (T ∩ N)_t`, which is therefore
  maximal in `N`.
- **"Every maximal torus in N is of this form".** This is part 2. If `S = (T ∩ N)_t` for a
  maximal torus `T` of `G`, then `S ⊆ T`. Conversely, if the maximal torus `S` of `N` lies in a
  maximal torus `T` of `G`, then `S ⊆ (T ∩ N)_t` as before, and maximality of `S` in `N` gives
  `S = (T ∩ N)_t`.

## Scope

- `G` need not be reductive, and `N` need not be connected.
- The statement does not construct `(T ∩ N)_t`. It states the two assertions through the
  containments `S ⊆ T`, which are equivalent to them as explained above.

## Related Library results

- `MaximalTorusBaseChangeStatement`
  ([`Torus.MaximalBaseChangeStatement`](MaximalBaseChangeStatement.md)) is Milne's Theorem
  17.82 for smooth affine `G`. It is proved as `maximalTorusBaseChange`
  ([`Torus.MaximalBaseChangeProof`](MaximalBaseChangeProof.md)).
- `MaximalTorusConjugacyStatement` in
  [`Absolute.BorelStatement`](../Absolute/BorelStatement.md) is Milne's Theorem 17.10, the
  conjugacy of maximal tori over an algebraically closed field used in Milne's proof. It is
  proved as `maximalTorusConjugacy`
  ([`Absolute.MaximalTorusConjugacyProof`](../Absolute/MaximalTorusConjugacyProof.md)).
