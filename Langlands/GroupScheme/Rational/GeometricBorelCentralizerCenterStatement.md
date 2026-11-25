# Statement: the centralizer of a Borel subgroup over an arbitrary field

`Langlands.GroupScheme.GeometricBorelCentralizerCenterStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsGeometricBorelSubgroup` and,
  through its imports, `IsBorelSubgroup` and the group-scheme vocabulary over a field.
- [`Rational.Characters`](Characters.md), for the centre `center G`.
- [`Rational.TorusNormalizer`](TorusNormalizer.md), for `SubgroupFunctor.centralizer`.

## Lean statement

```lean
def GeometricBorelCentralizerCenterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsGeometricBorelSubgroup i →
      (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (SubgroupFunctor.range i).centralizer.carrier T ↔
          ∃ y : T ⟶ B.X, y ∈ (center B).carrier T ∧ y ≫ i.hom.hom = x) ∧
        (SubgroupFunctor.range i).centralizer = center G
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`; `G.X.left` is the underlying scheme and `G.X.hom` its structure morphism.
  For a homomorphism `i : B ⟶ G`, `i.hom.hom : B.X ⟶ G.X` is the underlying morphism over `S`.
  A point of `G` over `T : Over S` is a morphism `T ⟶ G.X`.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsBorelSubgroup i` ([`Absolute.Borel`](../Absolute/Borel.md)): `i` is a closed immersion,
  `B` is smooth, connected and solvable, and `i` does not factor through a strictly larger
  smooth connected solvable closed subgroup.
- `IsGeometricBorelSubgroup i` ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)):
  `IsBorelSubgroup i` holds, and so does `IsBorelSubgroup` of the base change of `i` to an
  algebraic closure of `k`.
- `SubgroupFunctor.range i`: the points of `G` that factor through `i`.
- `F.centralizer` ([`Rational.TorusNormalizer`](TorusNormalizer.md)): a point `g` over `U` lies
  in it when, after every base change `a : V ⟶ U`, the point `a ≫ g` commutes with every point
  of `F` over `V`. So `(SubgroupFunctor.range i).centralizer` is the centralizer `C_G(B)`.
- `center G` ([`Rational.Characters`](Characters.md)): a point `g` over `T` lies in it when,
  after every base change `a : T' ⟶ T`, the point `a ≫ g` commutes with every point of `G` over
  `T'`.

## Statement and quantifiers

For every field `k : Type u`, every smooth, affine, connected group scheme `G` over `Spec k`
and every geometric Borel subgroup `i : B ⟶ G`:

1. for every scheme `T` over `Spec k` and every point `x` of `G` over `T`, `x` lies in the
   centralizer `C_G(B)` if and only if `x = y ≫ i.hom.hom` for a point `y` of the centre of
   `B` over `T`: `Z(B) = C_G(B)` as subgroups of `G`;
2. the centralizer `C_G(B)` equals the centre of `G`, as subgroup functors on all schemes over
   `Spec k`: `C_G(B) = Z(G)`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- 17.70, p.376: "Let B be a Borel subgroup of G. Then Z(B) = C_G(B) = Z(G) (17.22, 17.45)."
  It is in Section 17i, "Borel and parabolic subgroups over an arbitrary base field" (p.375),
  and the paragraph before it reads: "Let G be a connected group variety over k. Because the
  formation of centralizers and normalizers commutes with extension of the base field, the
  following statements can be deduced from the algebraically closed case."
- 17.66, p.375: "A Borel subgroup of a connected group variety G over k is a connected solvable
  subgroup variety B such that G/B is complete. … the Borel subgroups of G are exactly those
  algebraic subgroups that become Borel in the sense of (17.6) over an algebraic closure of k."
- Proposition 17.22, p.359 (Section 17b, over an algebraically closed field): "Let B be a Borel
  subgroup of G. Then Z(B) ⊂ C_G(B) = Z(G)."
- Proposition 17.45, p.365: "Let B be a Borel subgroup in a connected group variety G. Then
  Z(G) = Z(B)."
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns 17.22,
17.45 or 17.70.

Milne gives no separate proof of 17.70. He cites 17.22 and 17.45 and says, in the paragraph
quoted above, that the statement follows from the algebraically closed case because forming
centralizers commutes with extension of the base field. This is explanation only.

## Derivation from the source

- **Connected group variety over an arbitrary field.** No hypothesis on `k`; `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]` (Chapter 17 convention) and `[ConnectedSpace G.X.left]`.
- **Borel subgroup over `k`.** By 17.66 the Borel subgroups of `G` are the algebraic subgroups
  that become Borel over `k^a`; this is `IsGeometricBorelSubgroup i`. Its first component
  `IsBorelSubgroup i` follows mathematically from the second (the Library does not prove this):
  a smooth connected solvable closed subgroup of `G` containing `B` becomes one of `G_{k^a}`
  containing `B_{k^a}`, so it equals `B`.
- **Centres and centralizers.** Milne's `Z(B)`, `C_G(B)` and `Z(G)` are the functors on
  `k`-algebras of central, respectively centralizing, points. The Library's `center` and
  `SubgroupFunctor.centralizer` are their versions on all schemes over `Spec k`, with the
  commutation required after every base change.
- **`Z(B) = C_G(B)`.** `Z(B)` is a subgroup of `B`, viewed in `G` through `i`. Point (1) says
  that the points of `C_G(B)` are exactly the images under `i` of the points of `Z(B)`.
- **`C_G(B) = Z(G)`.** Point (2), an equality of subgroup functors of `G`.

## Scope

- `G` need not be reductive.
- Given point (2), point (1) is equivalent to the identity `Z(G) = Z(B)` of Proposition 17.45,
  stated in the Library as `BorelCenterEqualityStatement` (see below). Point (1) is kept so that
  the statement records Milne's full chain `Z(B) = C_G(B) = Z(G)`.

## Related Library results

- `BorelCentralizerCenterStatement`
  ([`Absolute.BorelCentralizerCenterStatement`](../Absolute/BorelCentralizerCenterStatement.md))
  states Proposition 17.22 over an algebraically closed field: `Z(B) ⊂ C_G(B) = Z(G)`.
- `BorelCenterEqualityStatement`
  ([`Absolute.BorelCenterEqualityStatement`](../Absolute/BorelCenterEqualityStatement.md))
  states Proposition 17.45 for geometric Borel subgroups over an arbitrary field: the points of
  `Z(G)` are exactly the images of the points of `Z(B)`.
