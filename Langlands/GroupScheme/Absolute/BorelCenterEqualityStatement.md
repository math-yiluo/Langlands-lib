# Statement: the centre of a Borel subgroup is the centre of the group

Worker 75.

`Langlands.GroupScheme.BorelCenterEqualityStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsGeometricBorelSubgroup` and,
  through its imports, `IsBorelSubgroup` and the group-scheme vocabulary over a field.
- [`Rational.Characters`](../Rational/Characters.md), for the centre `center G`.

## Lean statement

```lean
def BorelCenterEqualityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsGeometricBorelSubgroup i →
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (center G).carrier T ↔
          ∃ y : T ⟶ B.X, y ∈ (center B).carrier T ∧ y ≫ i.hom.hom = x
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`; `G.X.left` is the underlying scheme and `G.X.hom` its structure morphism.
  For a homomorphism `i : B ⟶ G`, `i.hom.hom : B.X ⟶ G.X` is the underlying morphism over `S`.
  A point of `G` over `T : Over S` is a morphism `T ⟶ G.X`.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsBorelSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed immersion, `B` is smooth,
  connected and solvable, and `i` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- `IsGeometricBorelSubgroup i` ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)):
  `IsBorelSubgroup i` holds, and so does `IsBorelSubgroup` of the base change of `i` to an
  algebraic closure of `k`.
- `center G` ([`Rational.Characters`](../Rational/Characters.md)): a point `g` over `T` lies in
  it when, after every base change `a : T' ⟶ T`, the point `a ≫ g` commutes with every point of
  `G` over `T'`.

## Statement and quantifiers

For every field `k : Type u`, every smooth, affine, connected group scheme `G` over `Spec k`
and every geometric Borel subgroup `i : B ⟶ G`: for every scheme `T` over `Spec k`, a point
`x` of `G` over `T` is central in `G` if and only if it is the image under `i` of a point `y`
of `B` over `T` that is central in `B`. In other words, the centre of `G` is the image under
`i` of the centre of `B`, as subgroup functors of `G` on all schemes over `Spec k`:
`Z(G) = Z(B)`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 17.45, p.365: "Let B be a Borel subgroup in a connected group variety G. Then
  Z(G) = Z(B)."
- Section 17d, opening, p.363: "The base field k need not be algebraically closed. An
  algebraic subgroup of a connected group variety G over k is Borel if it becomes Borel over
  k^a."
- Definition 17.6, p.353: over an algebraically closed field a Borel subgroup is a maximal
  connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns
Proposition 17.45.

Milne's proof: reduce to `k` algebraically closed. Since `Z(G) = C_G(B)` (17.22) and
`Z(B) = C_G(B) ∩ B`, it suffices that `Z(G) ⊆ B`; for a maximal torus `T ⊆ B`,
`Z(G) ⊆ C_G(T) ⊆ B` (17.39(b)). This is explanation only.

## Derivation from the source

- **Connected group variety over any field.** `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`,
  `[ConnectedSpace G.X.left]`, with no hypothesis on `k`, as in Section 17d.
- **Borel subgroups over `k`.** Milne's Section 17d convention, a subgroup that becomes Borel
  over `k^a`, is `IsGeometricBorelSubgroup i`. Mathematically its first component `IsBorelSubgroup i`
  follows from the second (the Library does not prove this): a smooth connected solvable
  closed subgroup of `G` containing `B` becomes one of `G_{k^a}` containing `B_{k^a}`, so it
  equals `B`.
- **Centres.** Milne's `Z(G)` and `Z(B)` are the subgroups representing the functors of
  central points on `k`-algebras. The Library's `center` is the all-test version on schemes
  over `Spec k`, with commutation required after every base change. The equality `Z(G) = Z(B)`
  of subgroups of `G` is read by transporting points of `Z(B)` along `i`; both inclusions are
  kept, as an `↔` on every test scheme.

## Related results

- Milne's Proposition 17.22 (`Z(B) ⊆ C_G(B) = Z(G)` over an algebraically closed field), an
  input to Milne's proof, is stated separately as `BorelCentralizerCenterStatement` in the
  module `Langlands.GroupScheme.Absolute.BorelCentralizerCenterStatement`.
- [`CentralIsogeny.BorelPreimage`](../CentralIsogeny/BorelPreimage.md) proves, for connected
  reductive groups over an algebraically closed field, that the centre lies in some Borel
  subgroup (`exists_isBorelSubgroup_center_le`).
