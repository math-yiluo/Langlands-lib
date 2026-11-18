# Wound unipotent groups over perfect fields

`Langlands.GroupScheme.PerfectFieldWoundUnipotentFiniteStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a perfect field (`[PerfectField k]`) and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth G.X.hom]` and
`[IsAffineHom G.X.hom]`. Assume `ConnectedSpace G.X.left` and
`IsUnipotent G`. The conclusion is

```text
HasConstantAffineLineMaps G ↔ IsFinite G.X.hom
```

In words, over a perfect field a connected unipotent group variety is wound
if and only if it is finite. Since `G` is connected and smooth, finite here
means trivial (see below).

The ingredients are existing declarations, used without change.

- `PerfectField k` (Mathlib) says that `k` is perfect.
- `Smooth G.X.hom` and `IsAffineHom G.X.hom` (Mathlib) say that the structure
  morphism `G.X.left ⟶ Spec k` is smooth and affine, and
  `ConnectedSpace G.X.left` says that the underlying space of `G` is
  connected. `IsFinite G.X.hom` (Mathlib) says that the structure morphism is
  finite.
- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector.
- `HasConstantAffineLineMaps G` (from
  [`Rational.AffineLineRigidity`](../Rational/AffineLineRigidity.md)) says
  that every morphism `f : AffineLine.scheme (Spec k) ⟶ G.X` in
  `Over (Spec k)`, that is, every morphism of `k`-schemes from the affine line
  `𝔸¹_k` to `G`, equals `toUnit _ ≫ c` for some
  `c : 𝟙_ (Over (Spec k)) ⟶ G.X`. Here `𝟙_ (Over (Spec k))` is the terminal
  object `Spec k`, so `c` is a `k`-point of `G` and `toUnit _ ≫ c` is the
  constant morphism with value `c`. For smooth connected unipotent groups
  this is woundness in the sense of Conrad–Gabber–Prasad, Definition B.2.1,
  as recorded in that module.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- 14.70, p.300: "In characteristic zero, the only wound unipotent group is
  the trivial group. Over a perfect field of characteristic p, the wound
  unipotent groups are those that are finite."
- Definition 14.69, p.299: "A connected unipotent group variety G is wound if
  every morphism from the affine line to G is constant."
- Section 14g, p.300: "This rest of this section is only a brief summary."
  Notes (c), p.300: "For a modern exposition of the material in this
  section, see Conrad et al. 2015, Appendix B."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- p.13, after Proposition 1.26: "Therefore 'group variety' = 'smooth
  algebraic group'."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Definition 14.69 on
printed p.299 and 14.70 on printed p.300 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.13 or 135.

Milne gives no proof. The reference he names is B. Conrad, O. Gabber and
G. Prasad, *Pseudo-reductive groups*, second edition (Cambridge University
Press, 2015), source ID `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 26.

- Definition B.2.1, p.568: "A smooth connected unipotent k-group U is
  k-wound if every map of k-schemes A¹_k → U is a constant map to a point in
  U(k)."
- Remark B.2.2, p.568: "Note that the definition of k-wound also makes sense
  in characteristic 0, where it is only satisfied by U = 1 (since a
  nontrivial smooth connected unipotent group in characteristic 0 always
  contains Ga as a subgroup over the ground field)."

The registered snapshot `conrad-author-books-errata-check-2026-11-02`
(SHA256
`0c7733b3533b07001d041f3065cfcf9d8a7fd117d4451a6b3ff9ff2399f8e710`) of the
Books section of Conrad's homepage lists the second edition with no errata
link. No correction to these passages is known.

A route to the statement: a nontrivial `G` contains a closed subgroup
isomorphic to `Ga`, by Milne 14.63 (with Definition 14.61) in characteristic
zero and by Milne Corollary 14.55 over a perfect field of characteristic `p`.
The morphism of schemes underlying such a subgroup is not constant, so a
wound `G` is trivial, hence finite. Conversely, a finite connected group
variety is trivial (see below), and the trivial group is wound. This is
explanation only. The statement does not depend on that route.

## Derivation from the source

- **Connected unipotent group variety.** A group variety is a smooth
  algebraic group (p.13), affine by the Chapter 14 convention. Definition
  14.69 defines woundness only for connected unipotent group varieties, so
  the statement assumes `Smooth G.X.hom`, `IsAffineHom G.X.hom`,
  `ConnectedSpace G.X.left` and `IsUnipotent G`. Smoothness gives local
  finite presentation and affineness gives quasi-compactness, so `G` is of
  finite type over `k`. Milne's unipotence is 6.45, which is `IsUnipotent`;
  its comparison is recorded in [`Reductive.Basic`](../Reductive/Basic.md).
- **Wound.** A morphism `f` from the affine line to `G` is constant in the
  sense of Definition 14.69 exactly when it is the composite of the structure
  morphism of the affine line with a `k`-point of `G`. Indeed, if the image
  of `f` is one point, that point is the image of the `k`-point `0`, so it is
  a `k`-point `x`, and since the affine line is reduced, `f` factors through
  the reduced closed subscheme `Spec k` at `x`. Conversely, such a composite
  has one-point image. This is the form of Definition B.2.1 of
  Conrad–Gabber–Prasad, and it is `HasConstantAffineLineMaps G`.
- **Perfect fields and characteristic zero.** A field of characteristic zero
  is perfect, so the statement covers both sentences of 14.70 with one
  hypothesis `PerfectField k`. Finiteness is "the wound unipotent groups are
  those that are finite". For the first sentence: a connected group variety
  that is finite over `k` is trivial. Its coordinate ring is a finite étale
  `k`-algebra, and since the underlying space is connected, the algebra is a
  field; it has a `k`-point (the identity), so it is `k` itself. So, for the
  groups in the statement, "finite" and "trivial" agree, and in
  characteristic zero the statement says that the only wound group is the
  trivial one.
- **Universes.** One universe `u` is used for `k` and the schemes. This is a
  formalization convention.

## Related Library results

- `Langlands.GroupScheme.UnipotentWoundCriterionStatement` (in
  [`Rational.UnipotentWoundCriterionStatement`](../Rational/UnipotentWoundCriterionStatement.md))
  states, over every field, that `HasConstantAffineLineMaps G` holds exactly
  when `G` has no central closed subgroup that is a one-dimensional vector
  group (Conrad–Gabber–Prasad, Proposition B.3.2).
- `Langlands.GroupScheme.PerfectFieldUnipotentSplitStatement` (in
  [`Unipotent.PerfectFieldSplitStatement`](PerfectFieldSplitStatement.md))
  states that over a perfect field every smooth connected unipotent group is
  split.
