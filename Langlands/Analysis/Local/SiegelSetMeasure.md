# Finite Haar measure of abstract Siegel-type sets

Author: Worker 1179.

This module is a helper for task 40747bb3, which proves
`Langlands.Global.AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement`. It contains
no adelic or algebraic-group content. It proves an abstract measure bound for sets of the shape
`ΩU ΩM C K` in a locally compact group, where `C` is a "chamber" of central elements of a Levi
factor. All declarations are in the namespace `Langlands.SiegelSetMeasure`.

## Intended use and provenance

The content is internal. It isolates the measure-theoretic part of the classical argument that
Siegel sets have finite Haar measure. Getz–Hahn 2024, Section 2.7 (printed pp. 71–72), defines
Siegel sets `Ω_N Ω_M A_{T₀}(t) K`. Moeglin–Waldspurger 1995, I.1.13 (printed p. 18), gives Haar
measure in Iwasawa coordinates as `dg = du m^{-2ρ₀} dm dk`, and finiteness of the Siegel-set
volume comes from integrating `δ(a)⁻¹` over the positive chamber. The route here avoids the
Iwasawa integration formula. It uses three ingredients:

1. a hypothesis `hc` bounding the Haar measure of right-`K`-saturated sets by a Haar measure of
   their trace on `Q`;
2. the Haar modulus of right translation inside `Q`;
3. a covering of the chamber by countably many translates of one compact box, with a geometric
   series bound.

The Lean formulation and proofs are internal and follow no textbook proof.

In the intended later specialization, none of which is proved here:

- the ambient group `H` is `G(𝔸)¹`;
- `Q = P(𝔸) ∩ G(𝔸)¹` for a minimal parabolic `P = M N`;
- `M` is `M(𝔸) ∩ G(𝔸)¹` and `U` is `N(𝔸)`;
- `K` is a good maximal compact subgroup with `G(𝔸) = P(𝔸) K`;
- `a` is the positive torus restricted to its norm-one part;
- the characters `λ_i` are the idelic norms of the simple roots;
- `e_i ≥ 1` comes from `δ_N(a) = ∏_{β > 0} |β(a)|^{m_β}`.

The hypothesis `hc` is the formula `dg = dq dk` for `G = Q K` with `K` compact. A separate module
proves it; this module does not import it.

## Declarations

### Sums (`section Sums`)

- `tsum_pi_prod_le f`: for a finite index type `ι` and `f : ι → ℕ → ℝ≥0∞`, the sum over all
  multi-indices `m : ι → ℕ` of `∏ i, f i (m i)` is at most `∏ i, ∑' n, f i n`.

  *Proof.* Write the `ℝ≥0∞` sum as the supremum of its finite partial sums. A finite set `s` of
  multi-indices lies in the box `Fintype.piFinset` of its coordinate projections. The box sum of a
  product equals the product of the coordinate sums (`Finset.prod_univ_sum`), and each finite
  coordinate sum is at most the full series.

### Dyadic index (`section Dyadic`)

- `dyadicIndex r : ℕ` is `Nat.log 2 ⌊r⌋₊`. For `r ≥ 1` it is the exponent `m` with
  `2 ^ m ≤ r < 2 ^ (m + 1)`. The two inequalities are `pow_dyadicIndex_le` and
  `lt_pow_dyadicIndex_succ`. Both are proved from Mathlib's `Int.zpow_log_le_self` and
  `Int.lt_zpow_succ_log_self`, using `Int.log_of_one_le_right` to identify `Int.log 2 r` with the
  natural-number logarithm.
- `div_mem_Icc_of_dyadicIndex_eq ht hr hs h`: let `t ≠ 0`, `t ≤ r` and `t ≤ s` in `ℝ≥0`, and
  suppose `r / t` and `s / t` have the same dyadic index. Then `1/2 ≤ r / s ≤ 2`. The proof writes
  `r / s = (r / t) / (s / t)` and uses that both quotients lie in `[2 ^ m, 2 ^ (m + 1))`.

### Chamber (`section Chamber`)

Let `A` be a group and `lam : ι → A →* ℝ≥0ˣ` finitely many positive characters.

- `chamber lam t` is the set `{x | ∀ i, t ≤ lam i x}`.
- `dyadicBox lam` is the set `{x | ∀ i, 1/2 ≤ lam i x ≤ 2}`.
- `chamberIndex lam t x : ι → ℕ` is the multi-index `i ↦ dyadicIndex (lam i x / t)`.
- `inv_mul_mem_dyadicBox ht hx hy h`: let `t ≠ 0`, let `x` and `y` lie in the chamber, and
  suppose they have the same chamber index. Then `y⁻¹ x` lies in the dyadic box. This is
  `div_mem_Icc_of_dyadicIndex_eq` applied coordinatewise, since `lam i (y⁻¹ x) = lam i x / lam i y`.
- `inv_prod_pow_le lam ht e he hy`: let `t ≠ 0`, let every exponent `e i ≠ 0`, and let `y` lie in
  the chamber. Then `(∏ i, lam i y ^ e i)⁻¹ ≤ ∏ i, (t ^ e i)⁻¹ 2^{-m_i}` in `ℝ≥0∞`, where `m` is
  the chamber index of `y`.

  *Proof.* From `2 ^ m_i ≤ lam i y / t` we get `t 2^{m_i} ≤ lam i y`. Raising to the power
  `e i ≥ 1` gives `t^{e_i} 2^{m_i} ≤ t^{e_i} (2^{m_i})^{e_i} ≤ (lam i y)^{e_i}`. The inverse
  reverses the inequality, and the inverse of a finite product of finite values is the product of
  the inverses.
- `tsum_prod_geometric_ne_top ht e`: for `t ≠ 0`, the sum over all `m : ι → ℕ` of
  `∏ i, (t ^ e i)⁻¹ 2^{-m_i}` is finite. The proof bounds it by the product of the coordinate
  series (`tsum_pi_prod_le`). Each coordinate series is `(t ^ e i)⁻¹ ∑ 2^{-n} = 2 (t ^ e i)⁻¹`,
  which is finite.

### Haar moduli and the main bound (`section Group`)

Let `H` be a second-countable, locally compact Hausdorff topological group with its Borel
σ-algebra. `HaarModulus.closedNormalizerCharacter U hU g` denotes the Library's Haar modulus of
the conjugation `u ↦ g u g⁻¹` on a closed subgroup `U`, for `g` in the normalizer of `U`.

- `mulEquivHaarChar_congr h₁ h₂ φ`: `mulEquivHaarChar φ` does not depend on which Borel
  σ-algebra instance is used. The two σ-algebras are equal by `BorelSpace.measurable_eq`.
- `coe_closedNormalizerCharacter hU g`: the value of `closedNormalizerCharacter U hU g` is
  `mulEquivHaarChar (normalizerConj U g)` computed with the subtype σ-algebra on `U`. The Library
  definition uses the local instance `borel U`, and `mulEquivHaarChar_congr` identifies the two.
- `closedNormalizerCharacter_eq_one_of_commute hM g hg`: if `g` commutes with every element of the
  closed subgroup `M`, its modulus on `M` is `1`. In that case the conjugation is the identity, and
  `mulEquivHaarChar_refl` applies.
- `measure_preimage_mul_right_inv hQ μQ W g`: let `Q` be a closed subgroup, `μQ` a Haar measure on
  `Q`, `W ⊆ Q` and `g ∈ Q`. Then `μQ (W g) = δ_Q(g)⁻¹ μQ(W)`, where `W g` is written as the
  preimage of `W` under `q ↦ q g⁻¹` and `δ_Q(g)` is the modulus of conjugation by `g` on `Q`.

  *Proof.* With `φ` conjugation by `g`, `φ⁻¹ W = g⁻¹ W g`, so `W g = g (φ⁻¹ W)`; in the Lean
  proof this is the preimage of `φ⁻¹ W` under `q ↦ g⁻¹ q`. Left invariance removes this left
  translation by `g`. Mathlib's `mulEquivHaarChar_smul_preimage` gives
  `mulEquivHaarChar φ · μQ (φ⁻¹ W) = μQ W`. That lemma needs `μQ` regular, which follows from
  `regular_of_isMulLeftInvariant` applied to a positive compact set, using second countability of
  `Q`.

- `measure_mul_mul_mul_lt_top` (**abstract Siegel-set bound**). The data are:
  - a measure `μ` on `H`;
  - closed subgroups `Q`, `M`, `U` with `IsSemidirectDecomposition Q M U`, so `Q = M ⋉ U`, and a
    continuous Levi projection `h.projection`;
  - a compact subgroup `K`;
  - a Haar measure `μQ` on `Q`.

  Assume the following:
  - `hc`: a constant `c` with `μ S ≤ c μQ (Q ∩ S)` for every measurable `S` with `S K ⊆ S`;
  - compact `ΩU ⊆ U`, `ΩM ⊆ M` and `B ⊆ M`;
  - a countable family `g n ∈ M`, each central in `M` and commuting with every element of `K ∩ Q`;
  - every `x ∈ C` has the form `g n * b` with `b ∈ B`;
  - `∑ₙ δ_U(g n)⁻¹ < ∞`.

  Then `μ (ΩU * ΩM * C * K) < ∞`.

  *Proof.* The set `ΩU ΩM C K` lies in the countable union of the compact sets
  `S n = ΩU ΩM (g n B) K`, each of which is right-`K`-saturated. Let `s = u m (g n b) k` be a point
  of `S n` that lies in `Q`. Then `k = (u m g n b)⁻¹ s ∈ Q`. Because `g n` commutes with `b` and
  with `k`, we get `s (g n)⁻¹ = u m b k`. So the trace `Q ∩ S n` lies in `W (g n)`, where `W` is
  the trace on `Q` of the fixed compact set `ΩU ΩM B (K ∩ Q)`. By `hc` and
  `measure_preimage_mul_right_inv`, `μ (S n) ≤ c δ_Q(g n)⁻¹ μQ W`. The Library theorem
  `IsSemidirectDecomposition.closedNormalizerCharacter_eq_mul` gives
  `δ_Q(g n) = δ_M(g n) δ_U(g n)`, and `δ_M(g n) = 1` by centrality. Summing over `n` with
  countable subadditivity gives `μ (ΩU ΩM C K) ≤ c (∑ₙ δ_U(g n)⁻¹) μQ W < ∞`.

- `measure_mul_chamber_mul_lt_top` (**chamber Siegel-set bound**). The data are:
  - the setting of the previous theorem;
  - a group `A` with a topology and a continuous homomorphism `a : A →* H` with values in `M`, central
    in `M` and commuting with every element of `K ∩ Q`;
  - finitely many characters `lam i` whose dyadic box is compact;
  - exponents `e i ≥ 1` with `∏ i, lam i x ^ e i ≤ δ_U(a x)` for all `x`.

  Then for every `t ≠ 0`, `μ (ΩU * ΩM * a(chamber lam t) * K) < ∞`.

  *Proof.* Index the cover by the set `J` of chamber indices that actually occur, and choose for
  each `κ ∈ J` a point `y κ` of the chamber with index `κ`. By `inv_mul_mem_dyadicBox`, every
  chamber point `x` with index `κ` satisfies `x = y κ · ((y κ)⁻¹ x)` with `(y κ)⁻¹ x` in the
  compact box. So `a(chamber)` is covered by the translates `a (y κ) · a(box)`. By `hδ` and
  `inv_prod_pow_le`, `δ_U(a (y κ))⁻¹ ≤ ∏ i, (t ^ e i)⁻¹ 2^{-κ_i}`. Summing over the injective
  family `κ ↦ κ` and using `tsum_prod_geometric_ne_top`, the series is finite.
  `measure_mul_mul_mul_lt_top` then applies.
