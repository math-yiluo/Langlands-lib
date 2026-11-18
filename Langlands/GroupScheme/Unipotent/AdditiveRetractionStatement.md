# Copies of `𝔾ₐ` in elementary unipotent groups are direct factors

`Langlands.GroupScheme.ElementaryUnipotentAdditiveRetractionStatement.{u}` is
a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field of characteristic `p`, with `[Fact p.Prime]` and
`[CharP k p]`, and write `𝔾ₐ` for
`VectorGroup.groupScheme (CommRingCat.of k) 1`. Let
`G : GroupScheme (Spec (CommRingCat.of k))`, `n : ℕ` and
`e : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) n` with
`IsClosedSubgroup e`. Then for every homomorphism `i : 𝔾ₐ ⟶ G` with
`IsClosedSubgroup i` there is a homomorphism `r : G ⟶ 𝔾ₐ` with

```text
i ≫ r = 𝟙 𝔾ₐ
```

In words, if `G` is elementary unipotent, every closed subgroup of `G`
isomorphic to `𝔾ₐ` is a direct factor of `G`.

The ingredients are existing declarations, used without change.

- `Fact p.Prime` and `CharP k p` (Mathlib) say that `k` has prime
  characteristic `p`.
- `VectorGroup.groupScheme (CommRingCat.of k) n` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the vector group
  `𝔾ₐⁿ = Spec k[T₁, …, T_n]` over `Spec k`, with the additive group law;
  for `n = 1` it is `𝔾ₐ`.
- `IsClosedSubgroup e` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of the homomorphism `e` is a closed
  immersion.
- `G ⟶ H` is the type of homomorphisms of group schemes over `Spec k`, and
  `≫` and `𝟙` are their composition and identity.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 14.47, p.295: "Let G be an elementary unipotent group. Every
  algebraic subgroup of G isomorphic to Ga is a direct factor of G."
- Definition 14.45, p.295: "An algebraic group is elementary unipotent if it
  embeds into a vector group V_a."
- Section 14e opening, p.292: "In this section, k is a field of
  characteristic p ≠ 0."
- Definition 5.41, p.108: "A homomorphism of algebraic groups is an embedding
  if it is a closed immersion."
- 2.6, pp.40–41: "For a k-vector space V, we let V_a denote the functor
  R ⇝ V ⊗ R." and, for finite-dimensional `V`, "The choice of a basis for V
  determines an isomorphism G_a^n → V_a."
- Definition 1.3, p.7: "An algebraic subgroup of an algebraic group (G, m_G)
  over k is an algebraic group (H, m_H) over k such that H is a k-subscheme
  of G and the inclusion map is a homomorphism of algebraic groups."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 14.47 on
printed p.295 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.7, 40, 41 or 108. Their p.18 entry concerns the
proof of Proposition 1.40, not Proposition 1.41.

Milne's proof: "An exact sequence e → Ga → G → Q → e corresponds to an exact
sequence 0 → P(Q) → P(G) → k_σ[F] → 0 of k_σ[F]-modules, which obviously
splits (choose a p ∈ P(G) mapping to 1 ∈ k_σ[F], and send a ∈ k_σ[F] to ap)."
Here `P(G)` is the module of homomorphisms `G → Ga` (Section 14e) and the
correspondence is Theorem 14.46. Here `P(Ga) = k_σ[F]`, with `1` the identity
homomorphism of `Ga`, so the element `p ∈ P(G)` mapping to `1` is a
homomorphism `G → Ga` restricting to the identity of `Ga`. This is explanation only. The statement does not depend on that
route.

## Derivation from the source

- **Field.** In Section 14e the field has characteristic `p ≠ 0`. The
  statement assumes `[Fact p.Prime]` and `[CharP k p]`.
- **Elementary unipotent group.** By Definition 14.45, `G` embeds into a
  vector group `V_a`, and by Definition 5.41 an embedding is a homomorphism
  that is a closed immersion. Here `V` is finite-dimensional: `V_a` is an
  algebraic group only then (2.6), and a basis identifies `V_a` with `𝔾ₐⁿ`.
  This is the hypothesis on `e`. A closed subgroup of `𝔾ₐⁿ` is affine and of
  finite type over `k`, so `G` is an algebraic group. It is commutative,
  since `e` is a monomorphism into a commutative group.
- **Algebraic subgroup isomorphic to `Ga`.** An algebraic subgroup `H` is a
  closed subscheme of `G` (Definition 1.3, Proposition 1.41), and an
  isomorphism `Ga ≅ H` composed with the inclusion of `H` is a homomorphism
  `i : 𝔾ₐ ⟶ G` that is a closed immersion. Conversely such an `i` is an
  isomorphism of `𝔾ₐ` onto the closed subgroup it defines. The statement
  quantifies over all such `i`.
- **Direct factor.** `G` is commutative. If `G = i(𝔾ₐ) × N` for a closed
  subgroup `N`, the projection onto the first factor, followed by the inverse
  of `i`, is a homomorphism `r` with `i ≫ r = 𝟙`. Conversely, given such an
  `r`, let `N` be the kernel of `r`. On points with values in any `k`-scheme
  `T`, the map `(a, x) ↦ i(a) · x` from `𝔾ₐ(T) × N(T)` to `G(T)` is a
  homomorphism, since `G` is commutative. It is bijective, with inverse
  `g ↦ (r(g), g · i(r(g))⁻¹)`. By the Yoneda lemma, `𝔾ₐ × N → G` is an
  isomorphism of group schemes. So "`i(𝔾ₐ)` is a direct factor of `G`" is
  equivalent to the existence of `r`, which is the conclusion.
- **Universes.** One universe `u` is used for `k` and the group schemes. This
  is a formalization convention.
