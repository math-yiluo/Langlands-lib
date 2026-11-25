# The Picard groups of SLₙ and GLₙ vanish

`Langlands.GroupScheme.LinearPicardTrivialStatement.{u}` is a Prop-valued
definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for every field `k : Type u` and every finite index type
`n : Type` with decidable equality, writing `PicardTrivial X` for the local
proposition

```text
∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle X,
  Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial X),
```

both of the following hold:

```text
PicardTrivial (SpecialLinear.groupScheme n (CommRingCat.of k)).X.left ∧
  PicardTrivial (GeneralLinear.groupScheme n (CommRingCat.of k)).X.left.
```

In words: over every field `k`, every line bundle on the scheme underlying
`SLₙ` is trivial, and every line bundle on the scheme underlying `GLₙ` is
trivial. So `Pic(SLₙ) = 0` and `Pic(GLₙ) = 0`.

Every ingredient is an existing declaration, used without change:

- `SpecialLinear.groupScheme n R` (from `Langlands.GroupScheme.SpecialLinear`)
  is the affine group scheme `SLₙ` over `Spec R`. Its underlying scheme is the
  spectrum of `SpecialLinear.CoordinateRing n R`, the polynomial ring in the
  entries `X (i, j)` modulo `det(X (i, j)) - 1`.
- `GeneralLinear.groupScheme n R` (from `Langlands.GroupScheme.GeneralLinear`)
  is the affine group scheme `GLₙ` over `Spec R`. Its underlying scheme is
  the spectrum of `GeneralLinear.CoordinateRing n R` (`groupScheme_left`).
  That ring is the polynomial ring in the entries of a matrix `X` and of a
  second matrix `Y`, modulo the entries of `XY - 1` and `YX - 1`.
- `Langlands.AlgebraicGeometry.Picard.LineBundle X` (from
  `Langlands.AlgebraicGeometry.Picard.LineBundle`) is the full subcategory of
  sheaves of `𝒪_X`-modules that are locally free of rank one: each point has an
  open neighbourhood `U` on which the sheaf is isomorphic to `𝒪_U`.
  `LineBundle.trivial X` is the structure sheaf `𝒪_X`. An isomorphism in
  `LineBundle X` is an isomorphism of the underlying module sheaves. The same
  encoding of `Pic(S) = 0` is used by the published
  `SplitTorusBorelIsomorphismStatement`.

The isomorphism classes of line bundles form the Picard group, and its
identity element is the class of `𝒪_X`. So `PicardTrivial X` says exactly
that this group is trivial. The group structure itself is not used.

The index type `n` may be any finite type. For `n = Fin m` this is Milne's
`SLₘ` and `GLₘ`. For empty `n`, both coordinate rings are polynomial rings in
no variables modulo the zero ideal, hence isomorphic to `k`. The proposition
then reduces to the triviality of line bundles on `Spec k`.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

- Proposition 20.30, printed p. 417 (PDF p. 433):

  > PROPOSITION 20.30. The Picard groups of SLn and GLn are zero.

  Milne's proof, on the same page, reads in full: "The polynomial ring
  k[X11, X12, …, Xnn] is a unique factorization domain (CA 4.10), and remains
  so after det(Xij) has been inverted. Therefore Pic(GLn) = 0. In 2.42 we saw
  that GLn ≃ SLn × Gm as schemes, from which it follows that Pic(SLn) = 0."
- Picard group, A.77, printed p. 584 (PDF p. 600): "Let X be an algebraic
  scheme over k. An invertible sheaf on X is a locally free O_X-module of rank
  1. The isomorphism classes of invertible sheaves on X form a group under
  tensor product, called the Picard group of X. It is denoted Pic(X)."
- 2.42, printed p. 53 (PDF p. 69): "The natural isomorphism of set-valued
  functors (A, r) ↦ A · diag(r, 1, …, 1) : SLn(R) × Gm(R) → GLn(R) defines an
  isomorphism of k-algebras O(GLn) ≃ O(SLn) ⊗ O(Gm)".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists
Chapter 20 corrections only on pp. 417, 419 and 420. The p. 417 entry concerns
the proof of 20.27 ("interchange second and third"), not 20.30. Its Chapter 2
corrections are only on pp. 48, 51 and 60, and its Appendix A corrections are
only on pp. 570 and 582 (footnote 3 and A.70). None concerns 20.30, 2.42 or
A.77.

The provenance is derived for three reasons:

1. Milne's invertible sheaves (A.77) are the Library's `LineBundle`s, the
   locally free rank-one module sheaves. "The Picard group is zero" is stated
   as: every line bundle is isomorphic to the trivial one.
2. Milne's `SLₙ` and `GLₙ` are the Library's group schemes
   `SpecialLinear.groupScheme` and `GeneralLinear.groupScheme` over
   `Spec k`, and the proposition concerns their underlying schemes. The
   natural number `n` is generalized to a finite index type, which loses
   nothing because every finite type is in bijection with some `Fin m`.
3. `k` lies in an arbitrary universe `u`. This is a formalization convention.

## For the proof (not part of this module)

The Library proves the proposition as
`LinearPicardTrivial.linearPicardTrivialStatement` in `LinearPicardTrivialProof`.
Milne's route can be followed. The Library supplies
`GeneralLinear.determinantLocalizationEquiv` in `GeneralLinearLocalization`;
the Picard comparisons below are the further steps of the proof.

- `GL_n`. The Library's coordinate ring `GeneralLinear.CoordinateRing n k` is
  isomorphic to the localization `k[Xᵢⱼ][1/det]`: the relation `XY = 1`
  forces `Y = X⁻¹`. A polynomial ring over a field is a unique factorization
  domain (Milne cites CA 4.10), and so is its localization at `det`. Mathlib's
  instance `Subsingleton (CommRing.Pic R)` for a domain `R` with
  `IsGCDMonoid R` (in `Mathlib.RingTheory.PicardGroup`; its docstring says
  that this includes unique factorization domains) then shows that the module
  Picard group is trivial.
- `SL_n`. By 2.42, `O(GLₙ) ≃ O(SLₙ) ⊗ k[T, T⁻¹]` as `k`-algebras, for `n`
  nonempty. The inclusion `O(SLₙ) → O(SLₙ)[T, T⁻¹]` has the retraction
  `T ↦ 1`. So the base-change map `Pic(O(SLₙ)) → Pic(O(GLₙ)) = 0` is split
  injective, and `Pic(O(SLₙ)) = 0`. Milne's "from which it follows" is this
  step. For empty `n`, the coordinate ring is isomorphic to the field `k`.
- From rings to schemes. The published
  `Langlands.AlgebraicGeometry.Picard.nonempty_lineBundle_iso_structureSheaf_of_pic_trivial`
  (in `Langlands.AlgebraicGeometry.Picard.AffineLineBundlePicard`) turns
  `Subsingleton (CommRing.Pic R)` into an isomorphism `L.obj ≅ 𝒪_{Spec R}` for
  every line bundle `L` on `Spec R`. That gives an isomorphism with
  `LineBundle.trivial (Spec R)` in the full subcategory `LineBundle`.
