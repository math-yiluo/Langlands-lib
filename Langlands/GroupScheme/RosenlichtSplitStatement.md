# Rosenlicht's criterion for split solvable groups

`Langlands.GroupScheme.RosenlichtSplitSolvableStatement.{u}` is a proposition
definition. This module defines the proposition and proves nothing.

## Statement

Let `k : Type u` be a field, put `S = Spec (CommRingCat.of k)`, and let
`G : GroupScheme S` satisfy `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and
`IsSolvableGroupScheme G`. If there are `n : ℕ` and a morphism of schemes
over `S`

```text
φ : (splitTorus S (ULift.{u} (Fin n))).X ⟶ G.X
```

whose underlying morphism of schemes `φ.left` is dominant (`IsDominant`),
then `IsSplitSolvableGroupScheme G`.

The ingredients are existing declarations, used without change.

- `IsSolvableGroupScheme G` (from [`Absolute.Borel`](Absolute/Borel.md)) says
  that the abstract group of `k̄`-points of the base change of `G` to
  `k̄ = AlgebraicClosure k` is solvable.
- `splitTorus S I` (from [`Torus.Split`](Torus/Split.md)) is the split torus
  `G_m^I` over `S`, the categorical product of copies of `G_m`; its
  underlying scheme is `(𝔸¹ ∖ 0)^I`.
- `IsDominant` (Mathlib) says that a morphism of schemes has dense image.
- `IsSplitSolvableGroupScheme G` (from [`SplitSolvable`](SplitSolvable.md))
  says that `G` is smooth, affine, connected and solvable, and has a finite
  series of closed, smooth, connected subgroups, each normal in the previous
  one with represented fppf quotient isomorphic over `k` to `G_a` or `G_m`,
  ending with the trivial group.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Theorem 16.58 (Rosenlicht), p.345: "A solvable group variety G is split if
  there exists a dominant map of schemes φ: (A^1 ∖ 0)^n → G for some integer
  n."
- p.13: "“group variety” = “smooth algebraic group”."
- Definition 6.33, p.132: "A solvable algebraic group G over k is split if it
  admits a subnormal series G = G_0 ⊃ G_1 ⊃ ⋯ ⊃ G_n = e such that each
  quotient G_i/G_{i+1} is isomorphic to G_a or to G_m."
- Corollary 6.31, p.132: "Assume that G is affine or smooth, and let k′ be a
  field containing k. Then G is solvable if and only if G_{k′} is solvable."
- Proposition 16.34, p.336, over an algebraically closed field: "(c) G is
  smooth and connected, and the abstract group G(k) is solvable; (d) G is
  smooth, connected, and solvable" are equivalent.
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Theorem 16.58 on
printed p.345 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for pp.13, 132, 336 or 345,
except that the 2022 errata's p.13 entry reverses a dimension inequality,
which is not the group-variety sentence (the reprint prints that sentence on
p.14). The 2017 errata's p.324 entry replaces "diagonalizable" with
"trigonalizable" in the first paragraph of Chapter 16; it does not concern
the affineness sentence, and the 2022 errata have no entry for p.324.

## Derivation from the source

- **Solvable group variety.** A group variety is a smooth algebraic group
  (p.13), affine by the Chapter 16 convention: `Smooth G.X.hom` (which gives
  locally of finite type) and `IsAffineHom G.X.hom` (quasi-compact, hence
  finite type). For solvability, `IsSolvableGroupScheme G` is used. The
  existence of a dominant map from the irreducible scheme `(𝔸¹ ∖ 0)^n`
  makes `G` irreducible, hence connected. For smooth connected `G`,
  Corollary 6.31 and Proposition 16.34 (c)⇔(d) over `k̄` identify Milne's
  solvability with `IsSolvableGroupScheme G` (`G_{k̄}` is connected since a
  connected algebraic group is geometrically connected).
- **The map.** `(A^1 ∖ 0)^n` is the underlying `k`-scheme of the split torus
  `G_m^n`, here `(splitTorus S (ULift.{u} (Fin n))).X`. A map of schemes is a
  morphism of `k`-schemes, that is, a morphism in `Over S`, and "dominant"
  is `IsDominant` of its underlying morphism of schemes. No compatibility
  with the group structures is required.
- **Split.** "G is split" is Definition 6.33; together with smoothness,
  connectedness, affineness and solvability, this is
  `IsSplitSolvableGroupScheme G`.
- **Universes.** One universe `u` is used for the field and the schemes; the
  index type `ULift.{u} (Fin n)` lives in it. This is a formalization
  convention.
