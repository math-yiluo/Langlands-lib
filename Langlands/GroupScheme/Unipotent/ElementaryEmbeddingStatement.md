# Smooth commutative groups of exponent `p` are elementary unipotent

`Langlands.GroupScheme.SmoothExponentElementaryUnipotentStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field of characteristic `p`, with `[Fact p.Prime]` and
`[CharP k p]`. Let `G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and `[IsCommMonObj G.X]`. Assume
that for every scheme `T` over `Spec k` and every point `g : T ⟶ G.X`,
`g ^ p = 1` in the group of `T`-points of `G`. The conclusion is

```text
∃ (n : ℕ) (e : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) n), IsClosedSubgroup e
```

so some homomorphism of group schemes from `G` to the vector group `𝔾ₐⁿ` is
a closed immersion. The field need not be perfect, and `G` need not be
connected.

The ingredients are existing declarations, used without change.

- `Fact p.Prime` and `CharP k p` (Mathlib) say that `k` has prime
  characteristic `p`.
- `Smooth G.X.hom` and `IsAffineHom G.X.hom` (Mathlib) say that the
  structure morphism `G.X.left ⟶ Spec k` is smooth and affine.
- `IsCommMonObj G.X` (Mathlib) says that the multiplication of `G` is
  unchanged when precomposed with the swap of the two factors of `G ×_k G`.
- `g ^ p` is the `p`-th power in the group `T ⟶ G.X` of `T`-points, the group
  structure induced by the group object `G` (Mathlib's
  `CategoryTheory.MonObj` scoped instances).
- `VectorGroup.groupScheme (CommRingCat.of k) n` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the vector group
  `𝔾ₐⁿ = Spec k[T₁, …, T_n]` over `Spec k`, with the additive group law.
- `IsClosedSubgroup e` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of the homomorphism `e` is a closed
  immersion.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 14.49, p.296: "Every smooth commutative algebraic group G of
  exponent p is elementary unipotent."
- Definition 14.45, p.295: "An algebraic group is elementary unipotent if it
  embeds into a vector group V_a."
- Section 14e opening, p.292: "In this section, k is a field of
  characteristic p ≠ 0."
- Definition 5.41, p.108: "A homomorphism of algebraic groups is an embedding
  if it is a closed immersion."
- 2.6, pp.40–41: "For a k-vector space V, we let V_a denote the functor
  R ⇝ V ⊗ R." and, for finite-dimensional `V`, "The choice of a basis for V
  determines an isomorphism G_a^n → V_a."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- Definition 1.24, p.12: "An algebraic group (G, m) is commutative if
  m ∘ t = m, where t is the transposition map (x, y) ↦ (y, x) : G × G →
  G × G."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 14.49 on
printed p.296 and Definition 14.45 on printed p.295 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.12, 40, 41 or 108.

Milne's proof: "Because G is smooth, V_G = 0 (see 11.41), and so G is
elementary unipotent by 14.48." Here `V_G` is the Verschiebung, and
Proposition 14.48 says that a commutative algebraic group is elementary
unipotent if and only if `V_G = 0`. This is explanation only. The statement
does not depend on that route.

## Derivation from the source

- **Field.** In Section 14e the field has characteristic `p ≠ 0`. The
  statement assumes `[Fact p.Prime]` and `[CharP k p]`.
- **Smooth commutative algebraic group.** An algebraic group is a group
  scheme of finite type over `k`, affine by the Chapter 14 convention. The
  statement assumes `Smooth G.X.hom`, `IsAffineHom G.X.hom` and
  `IsCommMonObj G.X` (Definition 1.24). Smoothness gives local finite
  presentation and affineness gives quasi-compactness, so `G` is of finite
  type over `k`.
- **Exponent `p`.** The hypothesis says that `g ^ p = 1` for all points `g`
  of `G` with values in any scheme over `k`. Taking `T = G.X` and `g` the
  identity morphism of `G.X`, this is the same as saying that the `p`-th power
  morphism `G → G` is the trivial homomorphism: `G` is killed by `p`. The
  hypothesis also admits the trivial group, which embeds into `𝔾ₐ⁰`.
- **Elementary unipotent.** By Definition 14.45, `G` embeds into a vector
  group `V_a`, and by Definition 5.41 an embedding is a homomorphism that is a
  closed immersion. Here `V` is finite-dimensional: `V_a` is an algebraic
  group only then (2.6), and a basis of `V` identifies `V_a` with `𝔾ₐⁿ`,
  `n = dim V`. Milne's `Ga` is `Spm(k[T])` with the group law `(R, +)`, and
  `𝔾ₐⁿ` is `VectorGroup.groupScheme (CommRingCat.of k) n`. So "elementary
  unipotent" is the conclusion `∃ n e, IsClosedSubgroup e`.
- **Universes.** One universe `u` is used for `k` and the schemes. This is a
  formalization convention.

## Related Library results

- `Langlands.GroupScheme.RelativeRoot.smoothCommutativePTorsionVector` (in
  [`Rational.CommutativePTorsionVectorProof`](../Rational/CommutativePTorsionVectorProof.md))
  proves `RelativeRoot.SmoothCommutativePTorsionVectorStatement`. Over an
  algebraically closed field it concludes that a smooth connected
  commutative group killed by `p` is a vector group. This statement allows
  every field of characteristic `p` and disconnected groups, and concludes
  only an embedding.
