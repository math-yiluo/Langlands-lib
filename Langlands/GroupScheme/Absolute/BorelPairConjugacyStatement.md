# Conjugacy of Borel pairs

`Langlands.GroupScheme.BorelPairConjugacyStatement.{u}` is a proposition
definition. This module defines the proposition and proves nothing.

## Statement

Let `k : Type u` be an algebraically closed field, put
`S = Spec (CommRingCat.of k)`, and let `G : GroupScheme S` satisfy
`[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`.
Let `B B' : GroupScheme S`, `T T' : CommGroupScheme S`, `i : B ⟶ G`,
`j : T.toGrp ⟶ G`, `i' : B' ⟶ G` and `j' : T'.toGrp ⟶ G` satisfy
`IsBorelPair i j` and `IsBorelPair i' j'`. Then there are a point
`g : Over.mk (𝟙 S) ⟶ G.X` and isomorphisms `φ : B ≅ B'` and `ψ : T ≅ T'`
with

```text
i ≫ (G.innerIso g).hom = φ.hom ≫ i'
j ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ψ.hom ≫ j'
```

The ingredients are existing declarations, used without change.

- `IsBorelPair i j` (from [`Absolute.Borel`](Borel.md)) says that `i` is a
  Borel subgroup (`IsBorelSubgroup i`), that `j` is a maximal torus
  (`IsMaximalTorus j`), and that `j` factors through `i`.
- `IsBorelSubgroup i` (same module) says that `i` is a closed subgroup
  (its underlying morphism of schemes is a closed immersion), that `B` is
  smooth, connected and solvable (`IsSolvableGroupScheme B`), and that `i`
  does not factor through a strictly larger smooth connected solvable closed
  subgroup.
- `IsMaximalTorus j` (from [`Torus.Maximal`](../Torus/Maximal.md)) says that
  `T` is a torus, that `j` is a closed subgroup, and that `j` does not
  factor through a strictly larger closed torus.
- `G.innerIso g` (from [`InnerAutomorphism`](../InnerAutomorphism.md)) is
  the inner automorphism of `G` given on points by `x ↦ g x g⁻¹`, with `g`
  pulled back to the test scheme. So `i ≫ (G.innerIso g).hom = φ.hom ≫ i'`
  says that conjugation by `g` carries the subgroup `B` onto `B'`, by the
  isomorphism `φ`. The second equation says the same for `T` and `T'`.
- `CommGroupScheme.groupHom` turns a morphism of commutative group schemes
  into a morphism of the underlying group schemes.
- `IsAlgClosed k` and `Smooth` are from Mathlib; `ConnectedSpace G.X.left`
  says that the underlying topological space of `G` is connected.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 17.13, p.356: "Any two Borel pairs of G are conjugate by an
  element of G(k)."
- Definition 17.12, p.355: "A pair (B, T) with T a maximal torus of G and B
  a Borel subgroup of G containing T is called a Borel pair."
- Section 17b, p.353: "In this section, G is a connected group variety over
  an algebraically closed field k."
- Definition 17.6, p.353: "A Borel subgroup of G is a maximal connected
  solvable subgroup variety of G."
- Chapter 17 opening, p.352: "Recall also that all algebraic groups are
  affine over a base field k".
- p.13: "“group variety” = “smooth algebraic group”."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."

Milne's proof, for orientation only: "Let (B, T) and (B′, T′) be Borel
pairs in G. Then gB′g⁻¹ = B for some g ∈ G(k) and bgT′g⁻¹b⁻¹ = T for some
b ∈ B(k), and so bg·(B′, T′)·(bg)⁻¹ = (B, T)." The first step is the
conjugacy of Borel subgroups, and the second is the conjugacy of maximal
tori in the smooth connected group `B` (a maximal torus of `G` contained in
`B` is a maximal torus of `B`).

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) has the Section 17b
convention and Definition 17.6 on printed p.354, and Definition 17.12 and
Proposition 17.13 on p.356, all with the same words. Its Chapter 17 opening
on p.352 contains the quoted affineness sentence with the same words, and
the quoted sentence on group varieties is on its p.14. Its Proposition 1.41
(p.19) is worded differently: "Algebraic subgroups of algebraic groups are
closed subschemes." This says the same for the present use.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.13, 352, 353,
355 or 356; their p.18 entry concerns the proof of Lemma 1.40, not
Proposition 1.41. The 2022 errata have no entry for reprint pp.14, 19, 352,
354 or 356.

## Derivation from the source

- **The group.** A connected group variety over `k` is a smooth algebraic
  group (p.13), affine by the Chapter 17 convention, with connected
  underlying space: `Smooth G.X.hom` (so `G` is locally of finite type),
  `IsAffineHom G.X.hom` (so quasi-compact, hence of finite type) and
  `ConnectedSpace G.X.left`. The field is algebraically closed throughout
  Section 17b.
- **Borel subgroups.** A subgroup variety of `G` is a smooth algebraic
  subgroup, and algebraic subgroups are closed (Proposition 1.41, p.18).
  So Definition 17.6 describes a smooth connected solvable closed subgroup
  that is maximal among such subgroups. This is `IsBorelSubgroup i`. For
  smooth affine groups, `IsSolvableGroupScheme` agrees with Milne's
  solvability, as explained in [`Absolute.Borel`](Borel.md).
- **Maximal tori.** Over the algebraically closed field `k`, a maximal
  torus of `G` is a torus of `G` not properly contained in another torus of
  `G`. Tori of `G` are closed subgroups (Proposition 1.41). This is
  `IsMaximalTorus j`; every torus is commutative, so `T` is a
  `CommGroupScheme S`.
- **Borel pairs.** "`B` containing `T`" says that `j` factors through `i`.
  With the two preceding bullets this is `IsBorelPair i j`.
- **Conjugacy.** "Conjugate by an element of `G(k)`" says that there is a
  single `g ∈ G(k)` with `g B g⁻¹ = B′` and `g T g⁻¹ = T′`. Equality of
  subgroups is expressed by isomorphisms `φ : B ≅ B'` and `ψ : T ≅ T'` over
  `G` after conjugation, as in the Library statements
  `BorelConjugacyStatement` and `MaximalTorusConjugacyStatement`. Milne
  conjugates the second pair onto the first; the statement conjugates the
  first onto the second. These are equivalent, by replacing `g` with `g⁻¹`.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
