# One-dimensional connected group varieties are commutative

`Langlands.GroupScheme.OneDimensionalCommutativeStatement.{u}` is a
proposition definition. Let `k` be any field and `G` an affine group scheme
over `Spec k`. Suppose its structure morphism is smooth of relative dimension
one and its underlying space is connected. The statement asserts that `G` is
commutative, which is Mathlib's `IsCommMonObj G.X`.

No proof is supplied here.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 14.25, p.286: "Every connected group variety of dimension one
  is commutative."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- p.13, after Proposition 1.26: "Therefore 'group variety' = 'smooth
  algebraic group'."
- Definition 1.24, p.12: "An algebraic group (G, m) is commutative if
  m ∘ t = m, where t is the transposition map (x, y) ↦ (y, x) : G × G →
  G × G."
- p.17, "The dimension of an algebraic group": the irreducible components of
  an algebraic group are its connected components, and "The dimension dim(G)
  of G is the common dimension of its connected components".

The 2022 corrected reprint of the same book (source ID
`milne-2022-algebraic-groups`; the one-based PDF page is the printed page
plus 11) states Proposition 14.25 on printed p.286 as "Every smooth connected
algebraic group of dimension one is commutative." This is the same
assertion. Its Chapter 14 opening, p.279, has the same affineness sentence.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316, so
neither corrects Proposition 14.25 or the Chapter 14 opening. The 2017
errata have no entry for pp.12, 13 or 17 either.

## Derivation from the source

- **Field.** Milne works over an arbitrary field `k`, and so does the
  statement. There are no characteristic or perfectness hypotheses.
- **Connected group variety.** An algebraic group in Milne is a group scheme
  of finite type over `k`. By the Chapter 14 convention it is affine. A
  group variety is a smooth algebraic group. The statement therefore assumes
  `IsAffineHom G.X.hom`, smoothness (through the relative-dimension
  instance) and `ConnectedSpace G.X.left`. Smoothness gives local finite
  presentation and affineness gives quasi-compactness, so `G` is of finite
  type over `k`.
- **Dimension one.** The instance `SmoothOfRelativeDimension 1 G.X.hom` says
  that `G` is smooth over `k` of relative dimension one at every point. For
  a scheme smooth over a field, the relative dimension at a point is the
  dimension of the scheme at that point. `G` is connected, so it is
  irreducible (Milne, p.17), and this is Milne's `dim(G) = 1`. Conversely, a
  connected group variety with `dim(G) = 1` is smooth of relative dimension
  one at every point.
- **Commutative.** Mathlib's `IsCommMonObj G.X` says that the multiplication
  of the group object `G.X` in the category of schemes over `Spec k` is
  unchanged when it is precomposed with the braiding (the swap of the two
  factors of `G ×_k G`). This is Milne's Definition 1.24.
- **Universes.** One universe `u` is used for `k` and the schemes. This is a
  formalization convention.

## Scope

- The statement assumes `G` affine, following the Chapter 14 convention. It
  says nothing about non-affine group varieties of dimension one, such as
  elliptic curves.
- Connectedness cannot be dropped. The normalizer of the diagonal torus in
  `SL₂` is smooth and affine of dimension one, but it is not commutative,
  since the Weyl element inverts the torus.
- Smoothness cannot be weakened to "dimension one" alone. In characteristic
  `p > 0`, the semidirect product `G_a ⋊ μ_p`, with `μ_p` acting on `G_a` by
  multiplication, is affine, connected (`μ_p` is infinitesimal) and of
  dimension one. It is not commutative.
