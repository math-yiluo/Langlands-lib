# Statement: points of a torus centralizer lie in Borel subgroups containing the torus

`Langlands.GroupScheme.TorusCentralizerBorelCoverStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup` and, through its imports,
  `IsClosedSubgroup` and the group-scheme vocabulary over a field.
- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), for `torusCentralizer`.
- [`Torus.Lattice`](../Torus/Lattice.md), for the field-level torus predicate `IsTorus`.

## Lean statement

```lean
def TorusCentralizerBorelCoverStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G),
    IsTorus S.toGrp → IsClosedSubgroup s →
    ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      g ∈ (torusCentralizer s).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) →
      ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
        (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X),
        IsBorelSubgroup i ∧ SubgroupFunctor.range s ≤ SubgroupFunctor.range i ∧
          b ≫ i.hom.hom = g
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `S.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism.
- **Rational points.** A morphism `g : Over.mk (𝟙 (Spec k)) ⟶ G.X` over `Spec k` is a point
  `g ∈ G(k)`.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`, `IsAlgClosed`: as in Mathlib.
- `IsTorus` ([`Torus.Lattice`](../Torus/Lattice.md)): a group scheme over `k` that becomes a
  split torus after base change to some field extension of `k` (Milne 12.14).
- `IsClosedSubgroup f` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `f` is a closed immersion.
- `torusCentralizer s` ([`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)): the
  centralizer `C_G(S)`; a point `g` over `U` lies in it when, after every base change
  `a : V ⟶ U`, `a ≫ g` commutes with every point of `S` over `V`.
- `IsBorelSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed subgroup, `B` is smooth,
  connected and solvable, and `i` is maximal among such closed subgroups (Milne 17.6).
- `SubgroupFunctor.range f`: the points of `G` that factor through `f`, on every test scheme;
  `range s ≤ range i` says that `B` contains `S`.

## Statement and quantifiers

For every algebraically closed field `k : Type u`, every smooth, affine, connected group scheme
`G` over `Spec k`, every closed torus `s : S ⟶ G` and every rational point `g ∈ G(k)` lying in
the centralizer `C_G(S)`: there are a Borel subgroup `i : B ⟶ G` whose range contains the range
of `s` and a rational point `b ∈ B(k)` with `i(b) = g`. In other words,
`C_G(S)(k) ⊆ ⋃_{B ⊇ S} B(k)`, the union over the Borel subgroups of `G` containing `S`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16. The 2022 corrected reprint has source ID `milne-2022-algebraic-groups`.

- Lemma 17.37, p.363 (2017): "Let T be a torus in a connected group variety G over an
  algebraically closed field k. Then C_G(T) ⊂ ⋃_{B ⊃ T} B (finite union over the Borel
  subgroups of G containing T)."
- Lemma 17.37, p.363 (2022 reprint): "Let S be a torus in a connected group variety G over an
  algebraically closed field k. Then C_G(S) ⊂ ⋃_{B ⊃ S} B (union over the Borel subgroups of G
  containing S)."
- Chapter 17 opening, p.352: "Recall that, when k is algebraically closed, we can identify the
  underlying topological space |G| of an algebraic group G with G(k). Recall also that all
  algebraic groups are affine over a base field k".
- Definition 17.6, p.353 (p.354 in the 2022 reprint): "A Borel subgroup of G is a maximal
  connected solvable subgroup variety of G."
- Remark after 1.26, p.13 (p.14 in the 2022 reprint): "“group variety” = “smooth algebraic
  group”."

**The change in the 2022 reprint.** The 2017 parenthetical "finite union" does not hold in
general. In `GL_2`, the scalar torus is contained in every Borel subgroup, and there are
infinitely many such subgroups, one for each line in `k²`. Its centralizer is all of `GL_2`,
which cannot be covered by finitely many Borel subgroups: `GL_2` is irreducible and each Borel
is proper closed. Finiteness can hold for a nonmaximal torus: in `𝔾_m × 𝔾_m` the first factor
is a proper subtorus and the ambient torus is the unique Borel. The 2022 reprint deletes
"finite". The Lean statement follows the reprint and makes no finiteness claim.

The official errata snapshot of 2026-11-02 for the 2017 printing (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for pp.13, 352, 353 or 363.
The errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`) has no entry for reprint pp.14, 352, 354 or
363.

Milne's proof uses the Borel fixed-point theorem on the locus of points in `G/B` fixed by
`c ∈ C_G(S)(k)`. This locus is nonempty because `c` lies in a Borel subgroup, which is conjugate
to `B`. It is closed in the complete variety `G/B` and is stable under `S`. An `S`-fixed point
`gB` there gives a Borel subgroup `gBg⁻¹` containing both `c` and `S`.

## Derivation from the source

- **Connected group variety over an algebraically closed field.** `[IsAlgClosed k]`,
  `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`: "group variety"
  is "smooth algebraic group", and Chapter 17 assumes algebraic groups are affine.
- **A torus in `G`.** A torus `S` with a closed immersion `s` (`IsTorus S.toGrp`,
  `IsClosedSubgroup s`), Milne's algebraic subgroup that is a torus.
- **The inclusion.** We use the rational-point reading of Milne's inclusion: over the
  algebraically closed field `k`, the closed points are the `k`-points. The statement
  quantifies over rational points `g` of `C_G(S)` and asks that `g` be the image of a rational
  point of a Borel subgroup `B` with `S ⊆ B`. It does not assert a covering of the scheme's
  nonclosed points or of the functor on all test schemes.
- **Borel subgroups.** `IsBorelSubgroup` is Definition 17.6. Containment of `S` in `B` is
  inclusion of subgroup functors, `range s ≤ range i`.

## Related Library results

- [`BorelPointContainmentStatement`](BorelPointContainmentStatement.md) (Milne 17.34) states that
  every rational point lies in a Borel subgroup, with no torus condition.
- [`TorusCentralizerBorelStatement`](TorusCentralizerBorelStatement.md) (Milne 17.46) relates
  Borel subgroups of `C_G(S)` to Borel subgroups of `G` containing `S`.
- [`TorusCentralizerBorelContainmentStatement`](TorusCentralizerBorelContainmentStatement.md)
  (Milne 17.29) states that, for a maximal torus `T`, `C_G(T)°` lies in every Borel subgroup
  containing `T`.
- [`IsTorus.connectedSpace_centralizer`](../Torus/CentralizerConnected.md) proves that torus
  centralizers are connected (Milne 17.38). Milne deduces 17.38 from Lemma 17.37; the Library
  proof uses a different route.
