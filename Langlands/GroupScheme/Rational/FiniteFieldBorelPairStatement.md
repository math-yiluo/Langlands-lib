# Statement: Borel pairs of connected group varieties over finite fields

`Langlands.GroupScheme.FiniteFieldBorelPairStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsGeometricBorelSubgroup` and,
  through its imports, `IsBorelSubgroup` and the group-scheme vocabulary over a field.
- [`Torus.Maximal`](../Torus/Maximal.md), for `IsMaximalTorus`.

## Lean statement

```lean
def FiniteFieldBorelPairStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
        (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
        IsGeometricBorelSubgroup b ∧ IsMaximalTorus j ∧
          SubgroupFunctor.range j ≤ SubgroupFunctor.range b) ∧
    ∀ (B B' : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (b' : B' ⟶ G)
      (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
      (j' : T'.toGrp ⟶ G),
      IsGeometricBorelSubgroup b → IsMaximalTorus j →
      SubgroupFunctor.range j ≤ SubgroupFunctor.range b →
      IsGeometricBorelSubgroup b' → IsMaximalTorus j' →
      SubgroupFunctor.range j' ≤ SubgroupFunctor.range b' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          SubgroupFunctor.range (b ≫ (G.innerIso g).hom) = SubgroupFunctor.range b' ∧
            SubgroupFunctor.range (j ≫ (G.innerIso g).hom) = SubgroupFunctor.range j'
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` the commutative
  group schemes; `T.toGrp` is the underlying group scheme of `T`. For `G : GroupScheme S`,
  `G.X` is its scheme over `S`, `G.X.left` the underlying scheme and `G.X.hom` the structure
  morphism. A point of `G` over `U : Over S` is a morphism `U ⟶ G.X`; a `k`-point is a
  morphism `Over.mk (𝟙 (Spec k)) ⟶ G.X`.
- `Finite k`, `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsBorelSubgroup b` ([`Absolute.Borel`](../Absolute/Borel.md)): `b` is a closed immersion,
  `B` is smooth, connected and solvable, and `b` does not factor through a strictly larger
  smooth connected solvable closed subgroup.
- `IsGeometricBorelSubgroup b` ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)):
  `IsBorelSubgroup b` holds, and so does `IsBorelSubgroup` of the base change of `b` to an
  algebraic closure of `k`.
- `IsMaximalTorus j` ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a torus, `j` is a closed
  immersion, and `j` does not factor through a strictly larger torus of `G` that is a closed
  immersion.
- `SubgroupFunctor.range i` for `i : H ⟶ G`: the subgroup functor of `G` whose points over `U`
  are the points of `G` over `U` that factor through `i`. `range j ≤ range b` says that every
  point of `G` factoring through `j` factors through `b`, over every scheme over `Spec k`; for
  closed immersions this says that `T` is contained in `B`. Equality of ranges says that the
  two closed subgroups coincide.
- `G.innerIso g` for a `k`-point `g` ([`InnerAutomorphism`](../InnerAutomorphism.md)): the
  inner automorphism `x ↦ g x g⁻¹` of `G` (`InnerAutomorphism.comp_innerIso_hom`). So
  `range (b ≫ int(g))` is the conjugate subgroup `g B g⁻¹`.

## Statement and quantifiers

Let `k : Type u` be a finite field and `G` a smooth, affine, connected group scheme over
`Spec k`. Call a pair `(b, j)` of a geometric Borel subgroup `b : B ⟶ G` and a maximal torus
`j : T ⟶ G` with `T ⊆ B` a Borel pair. Then:

1. `G` has a Borel pair: there are `B`, `b`, `T`, `j` with `b` a geometric Borel subgroup, `j`
   a maximal torus and `range j ≤ range b`;
2. any two Borel pairs `(b, j)` and `(b', j')` of `G` are conjugate by one `k`-point `g` of
   `G`: `g B g⁻¹ = B'` and `g T g⁻¹ = T'`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 17.99, p.383: "Let G be a connected group variety over k. There exists a Borel
  pair (B, T) in G, and any two Borel pairs are conjugate by an element of G(k)." It is in
  Section 17k, "Algebraic groups over finite fields" (p.382), and `k` is a finite field there,
  as in Corollaries 17.97 and 17.98 just before it and in its proof, which uses the Frobenius
  `σ` of `k` and Theorem 17.96.
- 17.66, p.375: "A Borel subgroup of a connected group variety G over k is a connected solvable
  subgroup variety B such that G/B is complete. … the Borel subgroups of G are exactly those
  algebraic subgroups that become Borel in the sense of (17.6) over an algebraic closure of k.
  A Borel pair of G is a pair that becomes a Borel pair over k^a in the sense of (17.12)."
- Definition 17.12, p.355 (over an algebraically closed field): "A pair (B, T) with T a maximal
  torus of G and B a Borel subgroup of G containing T is called a Borel pair." Definition 17.6,
  p.353: a Borel subgroup is a maximal connected solvable subgroup variety.
- Section 17d, p.363: over an arbitrary field, a maximal torus of `G` is a torus `T` with
  `T_{k^a}` maximal in `G_{k^a}`, which agrees with the obvious definition by Theorem 17.82,
  p.379.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns
Proposition 17.99.

## Milne's proof and two corrections

This section is explanation only. The Lean statement does not depend on it.

Milne's proof (p.384) has two parts. For existence, he takes a Borel subgroup `B` of `G_{k^a}`,
writes `σB = h B h⁻¹` with `h ∈ G(k^a)`, and uses Lang's theorem 17.96 to choose `g ∈ G(k^a)`
such that `g B g⁻¹` is fixed by `σ`. Then `g B g⁻¹` comes from a Borel subgroup of `G`. "The
existence of a maximal torus in B is proved similarly." For conjugacy, he takes `g ∈ G(k^a)`
with `(B₁, T₁)_{k^a} = g (B, T)_{k^a} g⁻¹` and uses Lang's theorem to correct `g` to a `k`-point.

Two steps of the printed proof are wrong as written, and the errata snapshot above does not
list them. Neither affects the proposition.

- **Orientation.** The proof writes `h = g⁻¹ σ(g)`. Since
  `σ(g B g⁻¹) = σ(g) h B h⁻¹ σ(g)⁻¹`, the equation that makes `g B g⁻¹` stable under `σ` is
  `h = σ(g)⁻¹ g`. This equation also has a solution `g`, by 17.96 applied to `h⁻¹`. With the
  printed equation the conclusion can fail. Take `k = F_3`, a generator `a` of `F_9^×`, the
  stabilizer `B` in `GL_2` of the line through `(1, a)`, `h = diag(1, a²)` and `g = diag(1, a)`.
  Then `σB = h B h⁻¹` and `h = g⁻¹ σ(g)`. But `g B g⁻¹` is the stabilizer of the line through
  `(1, a²)`, and its image under `σ` is the stabilizer of the line through `(1, a⁶)`, a different
  line.
- **Stabilizer.** The proof says that `g⁻¹ σ(g)` lies in `T(k^a)`. Applying `σ` to
  `(B₁, T₁)_{k^a} = g (B, T)_{k^a} g⁻¹` only shows that `g⁻¹ σ(g)` maps the pair `(B, T)_{k^a}` to
  itself, and the stabilizer of the pair can be larger than `T`. For example, take `G = B = G_a`
  and `T = 1`. Every `g ∈ k^a` fixes the pair, but `σ(g) - g ≠ 0` when `g ∉ k`. The argument
  works with `T` replaced by the centralizer `C_B(T)`. An element of `G(k^a)` that normalizes
  `B_{k^a}` and `T_{k^a}` lies in `B(k^a)` by the normalizer theorem 17.48. It then centralizes
  `T_{k^a}`, as shown in the proof of Proposition 17.53 (p.369). `C_B(T)` is connected by 16.41
  and smooth by 13.10, so it is a connected group variety over `k`. Lang's theorem 17.97 for
  `C_B(T)` gives `c ∈ C_B(T)(k^a)` with `g⁻¹ σ(g) = c σ(c)⁻¹`. Then `gc` is fixed by `σ`, so
  it lies in `G(k)`, and it conjugates `(B, T)` to `(B₁, T₁)`.

## Derivation from the source

- **Finite field; connected group variety.** `[Finite k]`; `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]` (Chapter 17 convention) and `[ConnectedSpace G.X.left]`.
- **Borel subgroups over `k`.** By 17.66 these are the algebraic subgroups that become Borel
  over `k^a`; this is `IsGeometricBorelSubgroup b`. Its first component `IsBorelSubgroup b`
  follows mathematically from the second (the Library does not prove this): a smooth
  connected solvable closed subgroup of `G` containing `B` becomes one of `G_{k^a}` containing
  `B_{k^a}`, so it equals `B`.
- **Maximal tori over `k`.** `IsMaximalTorus j`, the obvious definition. By Theorem 17.82,
  proved in the Library for smooth affine `G` as `maximalTorusBaseChange`
  ([`Torus.MaximalBaseChangeProof`](../Torus/MaximalBaseChangeProof.md)), it is equivalent to
  `T_{k^a}` being maximal in `G_{k^a}`, Milne's definition on p.363.
- **Borel pairs over `k`.** By 17.66 a Borel pair of `G` is a pair `(B, T)` of algebraic
  subgroups of `G` that becomes a Borel pair over `k^a`: `B_{k^a}` is a Borel subgroup, `T_{k^a}`
  a maximal torus, and `T_{k^a} ⊆ B_{k^a}`. By the two previous items the first two conditions
  are `IsGeometricBorelSubgroup b` and `IsMaximalTorus j`. Containment of closed subgroups can
  be checked over `k` or over `k^a` equally; the statement writes it over `k` as
  `range j ≤ range b`.
- **Conjugate by an element of `G(k)`.** One `k`-point `g` of `G` with `g B g⁻¹ = B'` and
  `g T g⁻¹ = T'`, both as equalities of subgroup functors of `G` on all schemes over `Spec k`.

## Scope

- The statement covers all smooth connected affine groups over finite fields, not only
  reductive ones. For connected reductive groups the existence part says that `G` is
  quasi-split, the remark after Proposition 17.99 ("every reductive group over a finite field
  is quasi-split").
- It does not state Lang's theorem itself.

## Related Library results

- `FiniteFieldQuasiSplitStatement`
  ([`Rational.FiniteFieldQuasiSplitStatement`](FiniteFieldQuasiSplitStatement.md)) states that
  every connected reductive group over a finite field is quasi-split, the remark after 17.99.
  It is proved as `finiteFieldQuasiSplit`
  ([`Rational.FiniteFieldQuasiSplit`](FiniteFieldQuasiSplit.md)).
- `FiniteFieldGeometricMaximalTorusStatement`
  ([`Torus.FiniteFieldGeometricMaximalStatement`](../Torus/FiniteFieldGeometricMaximalStatement.md))
  states that a smooth connected affine group over a finite field contains a torus that stays
  maximal over `k^a`, the torus part of the existence statement. It is proved as
  `finiteFieldGeometricMaximalTorus`
  ([`Torus.FiniteFieldGeometricMaximalProof`](../Torus/FiniteFieldGeometricMaximalProof.md)).
- `FiniteFieldTorsorPointStatement`
  ([`FiniteFieldTorsorPointStatement`](../FiniteFieldTorsorPointStatement.md)) is Lang's
  theorem in torsor form (Milne 17.98), proved as `finiteFieldTorsorPointStatement`
  ([`FiniteFieldTorsorPointProof`](../FiniteFieldTorsorPointProof.md)).
- `IsBorelPair` ([`Absolute.Borel`](../Absolute/Borel.md)) is the Borel pair predicate built
  from `IsBorelSubgroup` over `k` (maximality among smooth connected solvable subgroups over
  `k`). Over a non-algebraically-closed field this need not be Milne's 17.66 notion, so the
  statement does not use it.
