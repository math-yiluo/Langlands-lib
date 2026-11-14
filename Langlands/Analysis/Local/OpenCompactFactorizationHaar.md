# Haar measure of saturated sets when an open subgroup factors as `H₁ = (Q ∩ H₁) K`

Author: Worker 3994.

This module generalizes the Library lemma
`Langlands.CompactFactorization.exists_pos_measure_eq_of_mul_mem` (in
`Langlands/Analysis/Local/CompactFactorizationHaar.lean`). That lemma assumes the whole group
factors as `G = Q K`. Here only an open subgroup `H₁` needs to factor. The module is internal
supporting material for the finite-volume proof in
`Langlands/Global/AdelicFiniteVolumeProof.lean` and has no separate literature source. It
replaces a global Iwasawa decomposition `P(𝔸_F) K = G(𝔸_F)` with a local one.

## Setting

`G` is a Hausdorff, second-countable, locally compact topological group with its Borel
σ-algebra. All declarations live in the namespace `Langlands.CompactFactorization`.

## Declarations

- `subgroupOfInclusion Q H₁ : Q.subgroupOf H₁ →* Q`. For subgroups `Q` and `H₁` of `G`,
  this is the group homomorphism sending an element of `Q ⊓ H₁`, viewed as a subgroup of
  `H₁`, to the same element viewed in `Q`. The simp lemma `coe_subgroupOfInclusion` says
  that it does not change the underlying element of `G`.
- `isOpenEmbedding_subgroupOfInclusion`: if `H₁` is open in `G`, this inclusion is an open
  embedding.
  - It is an embedding because composing it with `Q → G` gives the composite of two subtype
    embeddings `Q.subgroupOf H₁ → H₁ → G`.
  - Its range is the preimage of `H₁` under `Q → G`, which is open.
- `exists_measure_inter_mul_eq_of_isOpen` (main result). Let `μ` be a Haar measure on `G`,
  and let:
  - `Q` be a closed subgroup;
  - `K` be a compact subgroup;
  - `H₁` be an open subgroup with `K ≤ H₁` such that every `g ∈ H₁` can be written
    `g = q k` with `q ∈ Q` and `k ∈ K`;
  - `μQ` be a Haar measure on `Q`.

  Then there is a constant `c : ℝ≥0` such that every measurable, right `K`-saturated set
  `A ⊆ G` (that is, `a k ∈ A` for all `a ∈ A`, `k ∈ K`) satisfies

  `μ (A ∩ Q H₁) = c · μQ (A ∩ Q)`,

  where `A ∩ Q` is read as the preimage of `A` in `Q`.

## Proof of the main result

1. **Haar measures on `H₁` and `Q ⊓ H₁`.**
   - `H₁` is open, hence also closed, locally compact and second countable. The pullback
     `μ₁` of `μ` along the open embedding `H₁ → G` is a Haar measure on `H₁`
     (`IsHaarMeasure.comap`).
   - In the same way, the pullback `μQ₁` of `μQ` along `subgroupOfInclusion Q H₁` is a Haar
     measure on `Q₁ = Q.subgroupOf H₁`.
2. **Factorization inside `H₁`.**
   - `Q₁` is closed in `H₁` and `K₁ = K.subgroupOf H₁` is compact.
   - Every `g ∈ H₁` is `q k` with `q ∈ Q` and `k ∈ K`. Then `q = g k⁻¹ ∈ H₁`, so
     `H₁ = Q₁ K₁`.
   - Applying the published `exists_pos_measure_eq_of_mul_mem` in `H₁` gives `c` with
     `μ₁ S = c · μQ₁ (S ∩ Q₁)` for every measurable right `K₁`-saturated `S ⊆ H₁`.
3. **Countably many cosets.** Let `O = H₁ ⊓ Q`, an open subgroup of `Q`.
   - `Q ⧸ O` is discrete. It is countable because it is separable (`Q` is second
     countable).
   - Fix a representative `r α ∈ Q` for each coset `α`. Then `Q H₁` is the disjoint union of
     the translates `r α · H₁`, and `Q` is the disjoint union of the translates `r α · O`.
4. **Each piece.** Put `P α = A ∩ r α · H₁` and `g = r α`.
   - `μ (P α) = μ (g⁻¹ A ∩ H₁)`, because `μ` is left invariant.
   - `μ (g⁻¹ A ∩ H₁) = μ₁ S` with `S = (g⁻¹ A) ∩ H₁` viewed in `H₁`. The set `S` is
     measurable and right `K₁`-saturated, since `A` is right `K`-saturated.
   - By step 2, `μ₁ S = c · μQ₁ (S ∩ Q₁)`.
   - Transporting through the open embedding `Q₁ → Q` and translating back by `g` (left
     invariance of `μQ`) gives `c · μQ ((A ∩ Q) ∩ r α · O)`.
5. **Summation.** By countable additivity in `G` and in `Q`:

   `μ (A ∩ Q H₁) = ∑' α, μ (P α) = c · ∑' α, μQ ((A ∩ Q) ∩ r α · O) = c · μQ (A ∩ Q)`.

Unlike the published lemma, this result does not assert `0 < c`. The finite-measure argument
only needs an upper bound.
