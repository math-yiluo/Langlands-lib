# A torus has a point with the same centralizer

`Langlands.GroupScheme.TorusGenericPointCentralizerStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be an algebraically closed field, put
`S = Spec (CommRingCat.of k)`, and let `G : GroupScheme S` satisfy
`[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`.
Let `T : CommGroupScheme S` and `j : T.toGrp ⟶ G` satisfy
`IsClosedSubgroup j` and `IsTorus T.toGrp`. Then there is a point
`s : 𝟙_ (Over S) ⟶ T.X` (a `k`-rational point of `T`) such that

```text
G.pointCentralizer (s ≫ j.hom.hom) = torusCentralizer j
```

as subgroup functors of `G`.

The ingredients are existing declarations, used without change.

- `G.pointCentralizer x` (from [`PointCentralizer`](../PointCentralizer.md))
  is the subgroup functor of points `c` of `G` over a test scheme `T'` that
  commute with the pullback of the base point `x` to `T'`.
- `torusCentralizer j` (from
  [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)) is the
  subgroup functor of points `g` of `G` over `T'` such that, for every
  morphism `a : V ⟶ T'` of test schemes and every point `t` of `T` over `V`,
  the pullback of `g` to `V` commutes with `j(t)`.
- `IsClosedSubgroup j` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `j` is a closed immersion.
- `IsTorus T.toGrp` (from [`Torus.Lattice`](Lattice.md)) says that `T`
  becomes a split torus (a finite product of copies of `G_m`) over some field
  extension of `k`.
- `IsAlgClosed k` and `Smooth` are from Mathlib; `ConnectedSpace G.X.left`
  says that the underlying topological space of `G` is connected.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Lemma 16.42, p.339: "Let S be a torus in a connected group variety G. There
  exists an s ∈ S(k) such that C_G(s) = C_G(S)."
- Section 16e, p.338: "Throughout, G is a connected group variety and k is
  algebraically closed."
- p.13: "“group variety” = “smooth algebraic group”."
- Definition 12.14, p.236: "An algebraic group over k is a torus if it
  becomes isomorphic to a finite product of copies of G_m over some field
  containing k."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

Milne's proof, for orientation only: with a faithful representation
`V = ⊕ V_{χ_i}` decomposed into eigenspaces of `S`, choose `s ∈ S(k)` outside
the proper closed subsets where `χ_i(s) = χ_j(s)` for `i ≠ j`. Then `C_G(s)`
is smooth (13.8), `C_G(s)(k) ⊂ C_G(S)(k)`, and `C_G(S) ⊂ C_G(s)`, so the two
are equal.

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Lemma 16.42 on
printed p.339 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for pp.236, 338 or 339, and the
2017 errata have no entry for p.13. The 2022 errata's p.13 entry reverses a
dimension inequality, not the group-variety sentence (which the reprint
prints on p.14). The 2017 errata's p.324 entry replaces "diagonalizable"
with "trigonalizable" in the first paragraph of Chapter 16; it does not
concern the affineness sentence.

## Derivation from the source

- **The group.** A connected group variety over `k` is a smooth algebraic
  group (p.13), affine by the Chapter 16 convention, with connected
  underlying space: `Smooth G.X.hom`, `IsAffineHom G.X.hom` (so `G` is of
  finite type) and `ConnectedSpace G.X.left`. The field is algebraically
  closed throughout Section 16e.
- **The torus.** A torus in `G` is an algebraic subgroup, hence a closed
  subgroup `j : T ⟶ G`, with `T` a torus (Definition 12.14). `T` is
  commutative, so it is given as a `CommGroupScheme`.
- **The point.** `s ∈ S(k)` is a morphism over `S` from the terminal object
  `𝟙_ (Over S)` (that is, `Spec k` itself) to `T`. Its image in `G` is
  `s ≫ j.hom.hom`.
- **The centralizers.** `C_G(s)` and `C_G(S)` are the scheme-theoretic
  centralizers, whose points over a `k`-algebra `R` are the elements of
  `G(R)` commuting with `s`, respectively with every point of `S` over every
  `R`-algebra. On all test schemes these are `G.pointCentralizer` and
  `torusCentralizer j`. Equality of closed subgroups is equality of these
  subgroup functors.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
