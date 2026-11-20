# A Borel subgroup is the normalizer of its unipotent part, on rational points

`Langlands.GroupScheme.BorelUnipotentNormalizerStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing. It states the part of Milne's Corollary 17.50 that holds: equality
on rational points. The scheme-theoretic equality printed by Milne is false
in general; see "A defect in the source" below.

## Statement

Let `k : Type u` be an algebraically closed field, put
`S = Spec (CommRingCat.of k)` and `pt = Over.mk (𝟙 S)`, and let
`G : GroupScheme S` satisfy `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and
`[ConnectedSpace G.X.left]`. Let `B U Q : GroupScheme S`, `i : B ⟶ G`,
`u : U ⟶ B` and `q : B ⟶ Q` satisfy

- `IsBorelSubgroup i`,
- `IsClosedSubgroup u`, `IsUnipotent U` and `(SubgroupFunctor.range u).IsNormal`,
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range u) q` and
  `IsMultiplicativeType Q`.

Then

```text
Subgroup.normalizer ((SubgroupFunctor.range (u ≫ i)).carrier pt : Set (pt ⟶ G.X))
  = (SubgroupFunctor.range i).carrier pt
```

that is, the normalizer in the abstract group `G(k)` of the image of `U(k)`
is the image of `B(k)`.

The ingredients are existing declarations, used without change.

- `IsBorelSubgroup i` (from [`Absolute.Borel`](Borel.md)) says that `i` is a
  closed subgroup, that `B` is smooth, connected and solvable
  (`IsSolvableGroupScheme B`), and that `i` does not factor through a
  strictly larger smooth connected solvable closed subgroup.
- `IsClosedSubgroup u` and `IsUnipotent U` (from
  [`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `u` is a closed immersion, and every nonzero finite-dimensional
  representation of `U` has a nonzero fixed vector.
- `SubgroupFunctor.range u` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of `B` whose points over a test scheme `T` are the
  images of points of `U`; `IsNormal` says that it is stable under
  conjugation by points of `B` over every test scheme. Its `carrier pt` is
  the subgroup of rational points `pt ⟶ B.X` in the image.
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel of `q` equals `N` on every test scheme.
- `IsMultiplicativeType Q` (from
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md)) says that
  `Q` becomes isomorphic to a diagonalizable group `D(Λ)`, with `Λ` a
  finitely generated commutative group, over some field extension of `k`.
- `Subgroup.normalizer` is Mathlib's normalizer of a subset of a group: the
  `g` with `g x g⁻¹ ∈ H ↔ x ∈ H` for all `x`. The group structure on the
  rational points `pt ⟶ G.X` is that of points of a group object.
- `IsAlgClosed k` and `Smooth` are from Mathlib; `ConnectedSpace G.X.left`
  says that the underlying topological space of `G` is connected.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 17.50, p.368: "Let B be a Borel subgroup of G and assume that B
  contains a subgroup B_u as in 16.7. Then B = N_G(B_u)."
- Its proof, p.368: "We may suppose that k is algebraically closed. Let
  P = N_G(B_u)_red. Then P contains B, and so it is connected (17.49). From
  the conjugacy of Borel subgroups, it follows that B_u is maximal among the
  connected unipotent subgroup varieties of G. Hence P/B_u has no nontrivial
  connected unipotent subgroup variety, and so it is a torus (17.25).
  Therefore P is solvable, and so P = B. Now,
  B = N_G(B_u)_red ⊂ N_G(B_u) ⊂ N_G(B) = B, and so N_G(B_u) = B."
- Section 17e, p.366: "Throughout, G is a connected group variety over a
  field k (not necessarily algebraically closed field)." Section 17d, p.363,
  defines a Borel subgroup over such a field as an algebraic subgroup that
  becomes Borel over `k^a`.
- Section 17b, p.353: "In this section, G is a connected group variety over
  an algebraically closed field k." Definition 17.6, p.353: "A Borel
  subgroup of G is a maximal connected solvable subgroup variety of G."
- Notation 16.7, p.326: "When G is an algebraic group, we use G_u
  exclusively to denote a normal algebraic subgroup such that G_u is
  unipotent and G/G_u is of multiplicative type."
- p.356: "Recall (16.33) that a connected solvable group variety H over a
  perfect field contains a unique normal unipotent algebraic subgroup such
  that H/H_u is of multiplicative type. Moreover, H_u is smooth and
  connected, and it is the largest unipotent algebraic subgroup of H."
- Proposition 1.83, p.31: "Let H be an algebraic subgroup of G. There is a
  unique algebraic subgroup N = N_G(H) of G such that, for all k-algebras
  R, N(R) = {g ∈ G(R) | gH_Rg⁻¹ = H_R}."
- Chapter 17 opening, p.352: "Recall also that all algebraic groups are
  affine over a base field k". p.13: "“group variety” = “smooth algebraic
  group”." Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups
  are closed (in the Zariski topology)."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) has Corollary 17.50 on
printed p.368 with the same words, Notation 16.7 on p.326, Proposition 1.83
on p.31, the Section 17e convention on p.366 and Definition 17.6 on p.354,
with the same words for the quoted statements and for the proof of 17.50.
The source defect described below is therefore present in both printings.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for p.326, 352, 353, 356, 366 or
368. The 2017 errata have no entry for p.31; the 2022 errata entry for p.31
corrects Corollary 1.81 ("closed in X" instead of "closed in G"), not
Proposition 1.83. The 2017 entry for p.18 concerns the proof of Lemma 1.40.

## A defect in the source

The scheme-theoretic equality `B = N_G(B_u)` is false for `G = PGL_2` over
an algebraically closed field of characteristic `2`. Let `B` be the image of
the upper triangular matrices and `B_u` the image `U` of the upper unitriangular
matrices; `U ≅ G_a` and `B/U ≅ G_m`. Over `R = k[ε]` (with `ε² = 0`) let
`g` be the image of `[[1, 0], [ε, 1]]`. For every `R`-algebra `R'` and
`t ∈ R'`,

```text
[[1, 0], [ε, 1]] · [[1, t], [0, 1]] · [[1, 0], [-ε, 1]] = [[1 - tε, t], [0, 1 + tε]]
                                                       = (1 + tε) · [[1, t - t²ε], [0, 1]]
```

in characteristic `2` (where `1 - tε = 1 + tε`). Modulo scalars this is the
point `[[1, t - t²ε], [0, 1]]` of `U`. The same computation holds for
`g⁻¹` (the image of `[[1, 0], [-ε, 1]] = [[1, 0], [ε, 1]]`). So `g` is a
point of `N_G(U)(R)` in the sense of Proposition 1.83, but `g` is not a point
of `B`, since its lower left entry is `ε ≠ 0` up to a unit. Hence
`N_G(B_u) ≠ B` as schemes. Infinitesimally: in `gl_2`, conjugating `E_{21}` by `[[1, t], [0, 1]]`
gives `E_{21} + t (E_{11} - E_{22}) - t² E_{12}`, and in characteristic `2` the element `E_{11} - E_{22}` is a scalar
matrix, which is zero in the Lie algebra of `PGL_2`. So the image of
`E_{21}` lies in the Lie algebra of `N_G(U)` but not in that of `B`.

In Milne's proof the step `N_G(B_u) ⊂ N_G(B)` fails: `g` above normalizes
`B_u` but not `B`. The earlier steps are correct and show that
`N_G(B_u)_red = B`. Over an algebraically closed field this is an equality
of rational points, which is the present statement.

## Derivation from the source

- **The group and the field.** A connected group variety is smooth (p.13),
  affine by the Chapter 17 convention, and connected: `Smooth G.X.hom`,
  `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`. Section 17e allows
  any field, with Borel subgroups defined over `k^a`; the statement covers
  only algebraically closed `k`, where Borel subgroups are those of
  Definition 17.6, that is, `IsBorelSubgroup i` (see
  [`Absolute.Borel`](Borel.md)).
- **The subgroup `B_u`.** Notation 16.7 asks for a normal algebraic
  subgroup of `B` that is unipotent with quotient of multiplicative type. An
  algebraic subgroup is closed (Proposition 1.41): `IsClosedSubgroup u`,
  `IsNormal` and `IsUnipotent U`. "`B/B_u` is of multiplicative type" means
  that there is a quotient map `q : B ⟶ Q` with kernel `B_u` and `Q` of
  multiplicative type: `IsFppfQuotient (range u) q` and
  `IsMultiplicativeType Q`, as in the published
  [`Unipotent.MultiplicativeExtensionPartStatement`](../Unipotent/MultiplicativeExtensionPartStatement.md).
  `B_u` is then unique, smooth and connected (16.33, quoted above; `k` is
  perfect).
- **Rational points.** Milne's proof gives `N_G(B_u)_red = B`. As `k` is
  algebraically closed, `N_G(B_u)` and its reduction have the same
  `k`-points, so `N_G(B_u)(k) = B(k)`. A point `g ∈ G(k)` lies in
  `N_G(B_u)(k)` exactly when `g B_u g⁻¹ = B_u`. As `B_u` is smooth, hence
  reduced and of finite type over the algebraically closed field `k`, it is
  determined by its `k`-points, so this holds exactly when
  `g B_u(k) g⁻¹ = B_u(k)` in `G(k)`. Thus the abstract normalizer of
  `B_u(k)` in `G(k)` is `B(k)`. This is the displayed equality: the carrier
  of `SubgroupFunctor.range (u ≫ i)` at `pt` is the image of `U(k)` in
  `G(k)`, and that of `SubgroupFunctor.range i` is the image of `B(k)`.
  The Library states the normalizer theorem 17.48 in the same form
  (`BorelNormalizerStatement` in
  [`Absolute.BorelStatement`](BorelStatement.md)).
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
