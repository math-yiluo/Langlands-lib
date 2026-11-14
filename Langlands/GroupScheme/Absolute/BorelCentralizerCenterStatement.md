# Statement: the centralizer of a Borel subgroup is the centre

Worker 75.

`Langlands.GroupScheme.BorelCentralizerCenterStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup` and the group-scheme vocabulary over a
  field.
- [`Rational.Characters`](../Rational/Characters.md), for the centre `center G`.
- [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md), for
  `SubgroupFunctor.centralizer`.

## Lean statement

```lean
def BorelCentralizerCenterStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
      (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ B.X), x ∈ (center B).carrier T →
          x ≫ i.hom.hom ∈ (SubgroupFunctor.range i).centralizer.carrier T) ∧
        (SubgroupFunctor.range i).centralizer = center G
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
- `SubgroupFunctor.range i`: the points of `G` that factor through `i`.
- `F.centralizer` ([`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md)): a point `g`
  over `U` lies in it when, after every base change `a : V ⟶ U`, the point `a ≫ g` commutes
  with every point of `F` over `V`.
- `center G` ([`Rational.Characters`](../Rational/Characters.md)): a point `g` over `T` lies in
  it when, after every base change `a : T' ⟶ T`, the point `a ≫ g` commutes with every point of
  `G` over `T'`.

## Statement and quantifiers

For every algebraically closed field `k : Type u`, every smooth, affine, connected group scheme
`G` over `Spec k` and every Borel subgroup `i : B ⟶ G`:

1. every point `x` of the centre of `B`, over any scheme `T` over `Spec k`, maps under `i` into
   the centralizer of `B` in `G`: `Z(B) ⊆ C_G(B)`;
2. the centralizer of `B` in `G` equals the centre of `G`, as subgroup functors on all schemes
   over `Spec k`: `C_G(B) = Z(G)`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 17.22, p.359: "Let B be a Borel subgroup of G. Then Z(B) ⊂ C_G(B) = Z(G)."
- Section 17b, opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k."
- Definition 17.6, p.353: a Borel subgroup is a maximal connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; p.13:
  "group variety" = "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. None concerns Proposition 17.22.

Milne's proof: the inclusions `Z(B) ⊂ C_G(B)` and `Z(G) ⊂ C_G(B)` are obvious; for
`g ∈ C_G(B)(R)`, the inner automorphism `inn(g)` is the identity on `B_R`, hence on `G_R` by
Proposition 17.21. This is explanation only.

## Derivation from the source

- **Connected group variety.** As in Section 17b: `[IsAlgClosed k]`, `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **Centres and centralizers.** Milne's `Z(B)`, `C_G(B)` and `Z(G)` are the functors on
  `k`-algebras of central, respectively centralizing, points. The Library's `center` and
  `SubgroupFunctor.centralizer` are their all-test versions on schemes over `Spec k`, with the
  commutation required after every base change. Point (1) transports a point of `Z(B)` into
  `G` along `i`, which is how the inclusion `Z(B) ⊂ C_G(B)` of subgroups of `G` reads.
- **Both assertions are kept.** Point (1) is the inclusion Milne calls obvious; point (2) is the
  substantive equality.

## Related results

- Milne's Proposition 17.21 (homomorphisms of `G_R` agreeing on `B_R` are equal), the input
  to Milne's proof, is stated separately as `BorelHomomorphismRigidityStatement` in the module
  `Langlands.GroupScheme.Absolute.BorelHomomorphismRigidityStatement`.
- [`Absolute.BorelStatement`](BorelStatement.md) states existence and conjugacy of Borel
  subgroups (17.9).
