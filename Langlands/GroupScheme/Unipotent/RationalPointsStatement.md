# Unipotence and rational points over perfect fields

`Langlands.GroupScheme.PerfectFieldUnipotentRationalPointsStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a perfect field (`[PerfectField k]`) and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Write
`UnipotentPoints` for the proposition

```text
∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
  (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
  IsNilpotent ((ρ.rationalMatrix g : Matrix n n k) - 1)
```

that every `k`-point of `G` acts by a unipotent matrix in every
finite-dimensional matrix representation of `G`. The statement is the
conjunction of:

1. `IsUnipotent G → UnipotentPoints`;
2. if `G(k)` is schematically dense in `G` and `UnipotentPoints` holds, then
   `IsUnipotent G`. Schematic density is the hypothesis: for every scheme
   `Z` and every closed immersion `z : Z ⟶ G.X.left` through which every
   `k`-point of `G` factors, `z` is an isomorphism.

The ingredients are existing declarations, used without change.

- `PerfectField k`, `LocallyOfFiniteType G.X.hom`, `IsAffineHom G.X.hom` and
  `IsClosedImmersion` (Mathlib).
- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector.
- `MatrixRepresentation G n` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `G ⟶ GL_n`.
- A morphism `g : Over.mk (𝟙 (Spec k)) ⟶ G.X` is a `k`-point of `G`, and
  `g.left : Spec k ⟶ G.X.left` is the underlying morphism of schemes.
- `ρ.rationalMatrix g` (from
  [`MatrixRepresentationRationalPoints`](../MatrixRepresentationRationalPoints.md))
  is the invertible matrix with entries in `k` by which `g` acts in `ρ`.
  `IsNilpotent (M - 1)` says that the matrix `M` is unipotent.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 14.10, p.282: "Let G be an algebraic group over a perfect field
  k. If G is unipotent, then all elements of G(k) are unipotent, and the
  converse is true when G(k) is dense in G (as a scheme)."
- Definition 1.9, p.9: "Let X be an algebraic scheme over k and S a subset of
  X(k). We say that S is schematically dense (or just dense) in X if the only
  closed subscheme Z of X such that S ⊂ Z(k) is X itself."
- Definition 14.27, p.286: "Let G be an algebraic group over k. An element u
  of G(k) is unipotent if r(u) is unipotent for all finite-dimensional
  representations r of G." The following paragraph, p.287: "When k is
  perfect, this agrees with the definition in 9.19."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k." and "Recall that an element r of a ring is unipotent
  if r − 1 is nilpotent."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 14.10 on
printed p.282 as "Let G be an algebraic group over a perfect field k. If G is
unipotent, then the elements of G(k) are unipotent, and the converse is true
when G(k) is schematically dense in G", making explicit the schematic
density meant in the 2017 text.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.9 or 135.

Milne's proof: choose a faithful finite-dimensional representation `(V, r)`
of `G`. If `G` is unipotent, then `r(G)` lies in `Uₙ` for some basis of `V`
(14.3), so each `r(g)` is unipotent and `g` is unipotent (9.19). Conversely,
if the elements of `G(k)` are unipotent, they act unipotently on `V`, so
`r(G(k)) ⊂ Uₙ(k)` for some basis (14.2), and since `G(k)` is dense in `G`,
`r(G) ⊂ Uₙ`. This is explanation only. The statement does not depend on
that route.

## Derivation from the source

- **Algebraic group over a perfect field.** Milne's algebraic group is a
  group scheme of finite type over `k`, affine by the Chapter 14 convention.
  The statement assumes `LocallyOfFiniteType G.X.hom` and
  `IsAffineHom G.X.hom`; an affine morphism is quasi-compact, so `G` is of
  finite type over `k`. Perfectness is `PerfectField k`.
- **Unipotent elements of `G(k)`.** In Corollary 14.10, unipotence of
  elements of `G(k)` refers to Section 9 (9.19), which over a perfect field
  agrees with Definition 14.27 (the paragraph after 14.27). By 14.27 an
  element is unipotent when it acts by a unipotent endomorphism in every
  finite-dimensional representation. A representation becomes a matrix
  representation once a basis is chosen, and an endomorphism is unipotent
  when its matrix minus the identity is nilpotent. This is `UnipotentPoints`.
- **Dense as a scheme.** Definition 1.9: `G(k)` is dense in `G` when the only
  closed subscheme `Z` of `G` with `G(k) ⊂ Z(k)` is `G` itself. In the
  statement a closed subscheme is given by a closed immersion
  `z : Z ⟶ G.X.left`, `G(k) ⊂ Z(k)` says that every `k`-point factors through
  `z`, and "is `G` itself" says that `z` is an isomorphism. Schematic density
  is needed: for `μ_p` in characteristic `p`, `μ_p(k)` is the identity alone,
  which is unipotent, and its single point is topologically dense, but `μ_p`
  is not unipotent (Milne, after 14.12, p.283).
- **Unipotent group.** Milne's definition is 6.45, which is `IsUnipotent`;
  its comparison is recorded in [`Reductive.Basic`](../Reductive/Basic.md).
- **Universes.** One universe `u` is used for `k` and the schemes, including
  the closed subschemes `Z`, and the index types `n` live in `Type`. A closed
  subscheme of `G` can be represented in universe `u`. This is a
  formalization convention.

## Related Library results

- `Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPoints` (in
  [`AlgebraicGeometry.PointTopology.RationalDensityStatement`](../../AlgebraicGeometry/PointTopology/RationalDensityStatement.md))
  is density of the rational points in the topological sense. It is weaker
  than schematic density for nonreduced groups and is not used here.
