# Split elementary unipotent groups are vector groups

`Langlands.GroupScheme.ElementaryUnipotentSplitIffVectorStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field of characteristic `p`, with `[Fact p.Prime]` and
`[CharP k p]`. Let `G : GroupScheme (Spec (CommRingCat.of k))`, `n : ℕ` and
`e : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) n` with
`IsClosedSubgroup e`. Then

```text
RelativeRoot.IsSplitUnipotent G ↔
  ∃ r : ℕ, Nonempty (G ≅ VectorGroup.groupScheme (CommRingCat.of k) r)
```

In words, an elementary unipotent group is split if and only if it is
isomorphic to `𝔾ₐʳ` for some `r`.

The ingredients are existing declarations, used without change.

- `Fact p.Prime` and `CharP k p` (Mathlib) say that `k` has prime
  characteristic `p`.
- `VectorGroup.groupScheme (CommRingCat.of k) n` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the vector group
  `𝔾ₐⁿ = Spec k[T₁, …, T_n]` over `Spec k`, with the additive group law.
- `IsClosedSubgroup e` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of the homomorphism `e` is a closed
  immersion.
- `RelativeRoot.IsSplitUnipotent G` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that `RelativeRoot.HasSplitSeries m G` holds for some `m`.
  `HasSplitSeries 0 G` says that `G` is trivial on all test schemes.
  `HasSplitSeries (m + 1) G` gives a smooth connected closed normal subgroup
  `j : K ⟶ G` and a homomorphism `q : G ⟶ V` that is flat, surjective and
  locally of finite presentation, whose kernel is the image of `j` on all
  test schemes, with `V` a one-dimensional vector group and
  `HasSplitSeries m K`.
- `≅` is an isomorphism in `GroupScheme (Spec (CommRingCat.of k))`, that is,
  an isomorphism of group schemes over `Spec k`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- 14.64, p.299: "An elementary unipotent group G over k is split if and only
  if it isomorphic to G_a^r for some r. This follows by induction from
  14.47." (The missing "is" is in the original.)
- Definition 14.61, p.299: "A unipotent algebraic group G over k is split if
  it admits a subnormal series each of whose quotients is isomorphic to Ga."
- 14.62, p.299: "A split unipotent algebraic group is automatically smooth
  and connected (8.1)."
- Definition 14.45, p.295: "An algebraic group is elementary unipotent if it
  embeds into a vector group V_a."
- Corollary 14.47, p.295: "Let G be an elementary unipotent group. Every
  algebraic subgroup of G isomorphic to Ga is a direct factor of G."
- Section 14e opening, p.292: "In this section, k is a field of
  characteristic p ≠ 0."
- Corollary 14.7, p.282: "Subgroups, quotients, and extensions of unipotent
  algebraic groups are unipotent." p.280: "In particular, Ga is unipotent and, in
  characteristic p, its subgroups α_p and Z/pZ are unipotent."
- Definition 5.41, p.108: "A homomorphism of algebraic groups is an embedding
  if it is a closed immersion."
- 2.6, pp.40–41: "For a k-vector space V, we let V_a denote the functor
  R ⇝ V ⊗ R." and, for finite-dimensional `V`, "The choice of a basis for V
  determines an isomorphism G_a^n → V_a."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states 14.64 and Definition
14.61 on printed p.299 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.40, 41 or 108.

## Derivation from the source

- **Field.** Elementary unipotent groups are defined in Section 14e, where
  the field has characteristic `p ≠ 0`. The statement assumes
  `[Fact p.Prime]` and `[CharP k p]`. Section 14g, which contains 14.64,
  imposes no further condition on `k`.
- **Elementary unipotent group.** By Definition 14.45, `G` embeds into a
  vector group `V_a`, and by Definition 5.41 an embedding is a homomorphism
  that is a closed immersion. Here `V` is finite-dimensional: `V_a` is an
  algebraic group only then (2.6), and a basis identifies `V_a` with `𝔾ₐⁿ`.
  This is the hypothesis on `e`. A closed subgroup of `𝔾ₐⁿ` is affine and of
  finite type over `k`. It is unipotent: `Ga` is unipotent (p.280), so
  `𝔾ₐⁿ` and its algebraic subgroups are unipotent (Corollary 14.7). So
  Definition 14.61 applies to `G`.
- **Split.** Definition 14.61 asks for a subnormal series
  `G = G₀ ⊃ G₁ ⊃ ⋯ ⊃ G_m = e` with `Gᵢ/Gᵢ₊₁ ≅ Ga`. Read from the top, this
  is the recursion in `HasSplitSeries`: `K = G₁` is a closed normal subgroup,
  the quotient map `q : G → V` has kernel `K`, `V ≅ Ga`, and `K` carries the
  rest of the series. `HasSplitSeries` also records that each `K` is smooth
  and connected; this holds for Milne's series by 14.62, since each `Gᵢ` is
  itself split. The quotient `V` is a one-dimensional vector group in the
  sense of `IsVectorGroupOfDimension V 1`: its points with values in every
  scheme `T` are naturally the additive group of global functions on `T`.
  This is `Ga` by the Yoneda lemma. So `IsSplitUnipotent G` is "G is split".
- **`G_a^r`.** Milne's `Ga` is `Spm(k[T])` with the group law `(R, +)`, and
  `G_a^r` is its `r`-fold product. This is
  `VectorGroup.groupScheme (CommRingCat.of k) r`. "Isomorphic" means
  isomorphic as algebraic groups, which is an isomorphism in
  `GroupScheme (Spec (CommRingCat.of k))`.
- **Universes.** One universe `u` is used for `k` and the group schemes. This
  is a formalization convention.
