# Statement: Borel subgroups of the centralizer of a torus

Worker 75.

`Langlands.GroupScheme.TorusCentralizerBorelStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsGeometricBorelSubgroup` and,
  through its imports, `IsBorelSubgroup`, `IsClosedSubgroup` and the group-scheme vocabulary
  over a field.
- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), for `torusCentralizer`.
- [`Torus.Lattice`](../Torus/Lattice.md), for the field-level torus predicate `IsTorus`.

## Lean statement

```lean
def TorusCentralizerBorelStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G),
    IsTorus S.toGrp → IsClosedSubgroup s →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      (torusCentralizer s).IsRepresentedBy c → IsClosedSubgroup c →
      (∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsGeometricBorelSubgroup b → SubgroupFunctor.range s ≤ SubgroupFunctor.range b →
          ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ C),
            IsGeometricBorelSubgroup d ∧
              SubgroupFunctor.range (d ≫ c) =
                SubgroupFunctor.range c ⊓ SubgroupFunctor.range b) ∧
      (IsAlgClosed k →
        ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ C), IsBorelSubgroup d →
          ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
            IsBorelSubgroup b ∧ SubgroupFunctor.range s ≤ SubgroupFunctor.range b ∧
              SubgroupFunctor.range (d ≫ c) =
                SubgroupFunctor.range c ⊓ SubgroupFunctor.range b)
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `S.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsTorus` ([`Torus.Lattice`](../Torus/Lattice.md)): a group scheme over `k` that becomes a
  split torus after base change to some field extension of `k` (Milne 12.14).
- `IsClosedSubgroup f` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `f` is a closed immersion.
- `torusCentralizer s` ([`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)): the
  centralizer `C_G(S)`; a point `g` over `U` lies in it when, after every base change
  `a : V ⟶ U`, `a ≫ g` commutes with every point of `S` over `V`.
- `F.IsRepresentedBy c` ([`SubgroupFunctor`](../SubgroupFunctor.md)): `c` is a monomorphism and
  `SubgroupFunctor.range c = F`.
- `SubgroupFunctor.range f`: the points of `G` that factor through `f`; subgroup functors are
  ordered by inclusion of points, and `⊓` is the pointwise intersection.
- `IsBorelSubgroup d` ([`Absolute.Borel`](Borel.md)): `d` is a closed immersion, its source is
  smooth, connected and solvable, and `d` does not factor through a strictly larger smooth
  connected solvable closed subgroup of the target.
- `IsGeometricBorelSubgroup d` ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)):
  `IsBorelSubgroup d` holds, and so does `IsBorelSubgroup` of the base change of `d` to an
  algebraic closure of `k`.

## Statement and quantifiers

Let `k : Type u` be a field, `G` a smooth, affine, connected group scheme over `Spec k`,
`s : S ⟶ G` a closed torus of `G`, and `c : C ⟶ G` a closed subgroup representing the
centralizer `C_G(S)`. Then:

1. for every geometric Borel subgroup `b : B ⟶ G` containing `S`, the intersection
   `C_G(S) ∩ B` is represented, through `c`, by a geometric Borel subgroup `d : D ⟶ C` of `C`:
   `range (d ≫ c) = range c ⊓ range b`;
2. if `k` is algebraically closed, every Borel subgroup `d : D ⟶ C` of `C` is of this form:
   there is a Borel subgroup `b : B ⟶ G` containing `S` with
   `range (d ≫ c) = range c ⊓ range b`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Theorem 17.46, pp.365-366: "Let G be a connected group variety over k. Let S be a torus in G
  and B a Borel subgroup containing S. Then C_G(S) ∩ B is a Borel subgroup of C_G(S). If k is
  algebraically closed, then every Borel subgroup of C_G(S) is of this form."
- Section 17d, opening, p.363: "The base field k need not be algebraically closed. An
  algebraic subgroup of a connected group variety G over k is Borel if it becomes Borel over
  k^a." The same section proves `C_G(T)` connected for every torus `T` (17.38), so `C_G(S)` is
  a connected group variety (smooth by 13.10) and has Borel subgroups in this sense.
- Definition 17.6, p.353: over an algebraically closed field a Borel subgroup is a maximal
  connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns Theorem
17.46.

Milne's proof: reduce to `k` algebraically closed. `C ∩ B = C_B(S)` is smooth, connected and
solvable; it is Borel in `C` because `CB` is closed in `G`, which follows from the rigidity
theorem (12.36) applied to `CB × S ⟶ B/B_u`. For the second part, all Borel subgroups of `C`
are conjugate under `C(k)` (17.9), and `c(B ∩ C)c⁻¹ = cBc⁻¹ ∩ C`. This is explanation only.

## Derivation from the source

- **Connected group variety over any field.** `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`,
  `[ConnectedSpace G.X.left]`, with no hypothesis on `k` for the first part and
  `IsAlgClosed k` as a hypothesis of the second part, as in the source.
- **A torus in `G`.** A torus `S` with a closed immersion `s` (`IsTorus S.toGrp`,
  `IsClosedSubgroup s`); Milne's algebraic subgroups are closed.
- **`C_G(S)`.** Any closed subgroup `c` representing `torusCentralizer s`. The statement
  quantifies over all such representatives; they are unique up to unique isomorphism over `G`.
- **Borel subgroups over `k`.** In the first part both Borel subgroups (of `G` and of `C`) are
  in Milne's Section 17d sense, `IsGeometricBorelSubgroup`. In the second part `k` is
  algebraically closed, where Milne's Borel subgroups are those of Definition 17.6,
  `IsBorelSubgroup`.
- **"`C_G(S) ∩ B` is a Borel subgroup of `C_G(S)`".** The intersection is the pointwise
  intersection of subgroup functors of `G`; the conclusion says that this intersection is the
  range, inside `G`, of a Borel subgroup of `C`. "Of this form" in the second part is the same
  equality for some Borel subgroup `B` of `G` containing `S`.

## Related Library results

- [`Absolute.CentralizerBorelIntersectionStatement`](CentralizerBorelIntersectionStatement.md)
  states a cocharacter version over an algebraically closed field: the centralizer of a
  cocharacter `χ` lying in a Borel subgroup `B` has a Borel subgroup inside `B`.
- [`Torus.CentralizerConnected`](../Torus/CentralizerConnected.md) proves that every
  representative of a torus centralizer in a smooth connected affine group over a field is
  connected (Milne 17.38).
