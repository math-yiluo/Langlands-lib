# Statement: the conjugates of a Borel subgroup cover the group

Worker 75.

`Langlands.GroupScheme.BorelConjugateCoverStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup` and the
group-scheme vocabulary over a field.

## Lean statement

```lean
def BorelConjugateCoverStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
      Surjective (fst G.X B.X * (snd G.X B.X ≫ i.hom.hom) * (fst G.X B.X)⁻¹).left
```

The module opens `CategoryTheory.MonoidalCategory`, `CategoryTheory.CartesianMonoidalCategory`
and the scoped `CategoryTheory.MonObj` notation, for `⊗`, `fst`, `snd` and the group law on
morphisms into a group object.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`; `G.X.left` is the underlying scheme and `G.X.hom` its structure morphism.
  For a homomorphism `i : B ⟶ G`, `i.hom.hom : B.X ⟶ G.X` is the underlying morphism over `S`.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`, `Surjective`: as in Mathlib. `Surjective f` for a
  morphism of schemes says that `f` is surjective on underlying points.
- `IsBorelSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed immersion, `B` is smooth,
  connected and solvable, and `i` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- **The conjugation morphism.** `fst G.X B.X, snd G.X B.X` are the projections of the product
  `G.X ⊗ B.X` (the fibre product over `Spec k`). Morphisms `G.X ⊗ B.X ⟶ G.X` form a group
  under the pointwise law of `G`, so
  `fst G.X B.X * (snd G.X B.X ≫ i.hom.hom) * (fst G.X B.X)⁻¹ : G.X ⊗ B.X ⟶ G.X`
  is the morphism `(g, b) ↦ g i(b) g⁻¹`, and `.left` is its underlying morphism of schemes. It
  is the same morphism as the Library's `BorelPointContainment.conjugation i`
  ([`Absolute.BorelPointContainmentDensity`](BorelPointContainmentDensity.md)); it is written
  out here to keep the imports small.

## Statement and quantifiers

For every algebraically closed field `k : Type u`, every smooth, affine, connected group scheme
`G` over `Spec k` and every Borel subgroup `i : B ⟶ G`, the conjugation morphism
`G × B ⟶ G`, `(g, b) ↦ g i(b) g⁻¹`, is surjective on underlying points.

**Why this is Milne's `|G| = ⋃ g|B|g⁻¹`.** Milne writes `|X|` for the space of closed points
of an algebraic scheme `X` (p.3), and over an algebraically closed field he identifies `|G|`
with `G(k)` (p.352). His union runs over `g ∈ G(k)`, so it is the set of closed points
`g i(b) g⁻¹` with `g ∈ G(k)` and `b ∈ B(k)`: the images of the `k`-points of `G × B` under
the conjugation morphism `c`. Milne makes the same identification in the proof of Lemma 17.32,
where the union is the image of `G × H` under `(g, h) ↦ ghg⁻¹`.

- The Lean statement implies Milne's. A closed point `x` of `G` has a preimage under `c`; its
  fibre is a nonempty scheme of finite type over `k`, so it has a `k`-point, and `x` is the
  image of a `k`-point of `G × B`.
- Milne's statement implies the Lean statement. The image of `c` is constructible (Chevalley),
  so its complement is a constructible subset of `G`. By Milne's statement this complement
  contains no closed point. A nonempty constructible subset of a scheme of finite type over a
  field contains a closed point (Jacobson property), so the complement is empty.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Theorem 17.33(b), p.362: "Let B be a Borel subgroup of G. Then |G| = ⋃_{g∈G(k)} g|B|g⁻¹."
- Section 17c, opening, p.361: "In this section, G is a connected group variety over k
  algebraically closed."
- Lemma 17.32 and its proof, pp.361-362: the union `⋃ g|H|g⁻¹` is the image of
  `G × H ⟶ G/H × G ⟶ G`, `(g, h) ↦ (ḡ, ghg⁻¹) ↦ ghg⁻¹`.
- Notation, p.3: "By a 'point' of an algebraic scheme or variety over k we always mean a closed
  point. … |X| the underlying topological space of closed points."
- Chapter 17 opening, p.352: over an algebraically closed field `|G|` is identified with
  `G(k)`, and all algebraic groups are affine over the base field.
- Definition 17.6, p.353: a Borel subgroup is a maximal connected solvable subgroup variety;
  remark after 1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns Theorem
17.33.

Milne's proof: for a maximal torus `T ⊆ B`, `C_G(T)° ⊆ B` (17.29), so by part (a) the union of
the conjugates of `B` contains a nonempty open subset of `G`; it is closed because `G/B` is
complete (Lemma 17.32(a)), hence equals `G`. This is explanation only.

## Derivation from the source

- **Connected group variety.** As in Section 17c: `[IsAlgClosed k]`, `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **The union of conjugates.** Stated as surjectivity of the conjugation morphism on all
  points of `G`, which is equivalent to Milne's closed-point statement as explained above.
- **Part (a) of Theorem 17.33** (the conjugates of `C_G(T)°` contain a nonempty open subset)
  is not stated here. For a maximal torus `T`, `C_G(T)` is connected (Library
  `IsTorus.connectedSpace_centralizer`, [`Torus.CentralizerConnected`](../Torus/CentralizerConnected.md)),
  so `C_G(T)° = C_G(T)` is a Cartan subgroup and part (a) is the density assertion of
  Proposition 17.44, stated separately as `CartanConjugacyDensityStatement` in the module
  `Langlands.GroupScheme.Cartan.ConjugacyDensityStatement`.

## Related Library results

- [`Absolute.BorelPointContainmentStatement`](BorelPointContainmentStatement.md) states the
  first sentence of Corollary 17.34: every `k`-point of `G` lies in some Borel subgroup.
  Together with the conjugacy of Borel subgroups this gives the closed-point form of Theorem
  17.33(b).
- [`Absolute.BorelStatement`](BorelStatement.md) states existence and conjugacy of Borel
  subgroups (Theorem 17.9).
