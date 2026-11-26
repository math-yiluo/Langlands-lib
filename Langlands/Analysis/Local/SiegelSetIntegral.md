# Weighted integrals over abstract Siegel-type sets

Module `Langlands.Analysis.Local.SiegelSetIntegral`, namespace `Langlands.SiegelSetMeasure`.

This module is a weighted companion of `Langlands/Analysis/Local/SiegelSetMeasure.lean`. That
module bounds the Haar *measure* of an abstract Siegel set `ΩU ΩM a(C) K`. This one bounds the
*integral* of a nonnegative measurable function over such a set, when the function is dominated
by the modulus `δ_U(a(x))` times a weight of the dyadic position of `x`. It contains no adelic or
algebraic-group content. Its adelic use is
`Langlands.Global.AdelicSiegelFactors.exists_lintegral_centralSiegelSet_le`
(`Langlands/Global/AdelicSiegelDominatedIntegrabilityProof.lean`).

## Provenance

The content is internal and derived. Moeglin–Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), I.1.13 (printed p. 18), write Haar measure in Iwasawa coordinates as
`dg = du m^{-2ρ₀} dm dk`. With this formula, an integrand bounded by `δ(a) Φ(a)` on a Siegel set
has integral bounded by a constant times `∫ Φ(a) da` over the chamber, because the factor `δ(a)`
cancels the Haar density `δ(a)⁻¹`. The module proves a discrete form of this statement without
the Iwasawa integration formula. It follows the route of `SiegelSetMeasure`: the measure of
right-`K`-saturated sets is bounded by a Haar measure of their trace on `Q` (hypothesis `hc`),
the Haar modulus of right translation inside `Q` is computed by
`SiegelSetMeasure.measure_preimage_mul_right_inv`, and the chamber is covered by countably many
translates of one compact box. The new ingredient is that the boxes are indexed by integer
dyadic indices in all coordinates, so the cover also handles directions in which the torus is
not bounded below, such as the split centre.

## Declarations

### Measure theory

- `setLIntegral_le_mul_of_forall_le`: if `f` is measurable and `f ≤ c` on a set `s`, then
  `∫⁻ x in s, f x ∂μ ≤ c μ(s)`. The set `s` need not be measurable. *Proof.* The set
  `{c < f}` is measurable, so `μ.restrict s {c < f} = μ({c < f} ∩ s) = μ(∅) = 0`
  (`Measure.restrict_apply`). Hence `f ≤ c` almost everywhere for `μ.restrict s`, and
  `lintegral_mono_ae` with `setLIntegral_const` gives the bound.

### Integer dyadic indices

- `div_mem_Icc_of_log_eq`: two positive reals `r, s` in `ℝ≥0` with `⌊log₂ r⌋ = ⌊log₂ s⌋`
  (Mathlib's `Int.log 2`) satisfy `1/2 ≤ r/s ≤ 2`. Both lie in `[2^k, 2^{k+1})`
  (`Int.zpow_log_le_self`, `Int.lt_zpow_succ_log_self`).
- `zIndex lam x : ι → ℤ` is `i ↦ Int.log 2 (λ_i(x))` for characters `λ_i : A →* ℝ≥0ˣ`.
- `inv_mul_mem_dyadicBox_of_zIndex_eq`: if `x` and `y` have the same integer dyadic index, then
  `y⁻¹ x` lies in the box `dyadicBox lam = {1/2 ≤ λ_i ≤ 2}` of `SiegelSetMeasure`, since
  `λ_i(y⁻¹ x) = λ_i(x)/λ_i(y)`.

### The weighted bound

The setting is that of `SiegelSetMeasure.measure_mul_mul_mul_lt_top`: `H` is a Hausdorff,
second-countable, locally compact group with its Borel σ-algebra, `μ` is a measure on `H`, `Q`,
`M`, `U` are closed subgroups with `IsSemidirectDecomposition Q M U` and continuous Levi
projection, `K` is a compact subgroup, `μQ` is a Haar measure on `Q`, and
`hc : μ S ≤ c μQ(S ∩ Q)` for every measurable right-`K`-saturated `S`. The sets `ΩU ⊆ U` and
`ΩM ⊆ M` are compact. `δ_U(g)` is the Library's `HaarModulus.closedNormalizerCharacter` of `U`.

- `measure_piece_le`: for a compact `B ⊆ M` and `g ∈ M` central in `M` and commuting with
  `K ∩ Q`,
  `μ(ΩU ΩM (g B) K) ≤ c δ_U(g)⁻¹ μQ(W)`, where `W` is the trace on `Q` of the compact set
  `ΩU ΩM B (K ∩ Q)`. *Proof.* This is the per-piece estimate inside the proof of the published
  `measure_mul_mul_mul_lt_top`, isolated for one `g`. If `s = u m (g b) k` lies in `Q`, then
  `k ∈ Q`, and since `g` commutes with `b` and `k`, `s g⁻¹ = u m b k ∈ W`. So the trace of the
  piece on `Q` lies in the right translate `W g`. Apply `hc`, then
  `measure_preimage_mul_right_inv`, and finally `δ_Q(g) = δ_M(g) δ_U(g) = δ_U(g)`
  (`IsSemidirectDecomposition.closedNormalizerCharacter_eq_mul` and
  `closedNormalizerCharacter_eq_one_of_commute`).
- `exists_lintegral_chamber_le` (**weighted chamber bound**). Let `a : A →* H` be continuous with
  values in `M`, central in `M` and commuting with `K ∩ Q`, and let `λ_i` (`i ∈ ι`, finite) be
  characters of `A` whose dyadic box is compact, with exponents `e_i` such that
  `δ_U(a(x)) ≤ ∏_i λ_i(x)^{e_i}` for all `x`. Then there is `D < ∞` such that for every
  `C ⊆ A`, every measurable `f : H → [0, ∞]` and every `Φ : ℤ^ι → [0, ∞]` with
  `f(u m a(x) k) ≤ δ_U(a(x)) Φ(zIndex lam x)` for `x ∈ C`, `u ∈ ΩU`, `m ∈ ΩM`, `k ∈ K`,

  `∫⁻ y in ΩU ΩM a(C) K, f y ∂μ ≤ D ∑_{κ ∈ ℤ^ι} Φ(κ)`.

  *Proof.* Put `B = a(box)`, `W` as above and `D = 2^{∑ e_i} c μQ(W)`. For each index `κ` that
  occurs on `C`, choose `y_κ ∈ C` with that index, and let `P_κ` be the set of points
  `u m a(x) k` with `x ∈ C` of index `κ`. These sets cover `ΩU ΩM a(C) K`.
  - By `inv_mul_mem_dyadicBox_of_zIndex_eq`, `x = y_κ b` with `b` in the box, so
    `P_κ ⊆ ΩU ΩM (a(y_κ) B) K`. By `measure_piece_le`, `μ(P_κ) ≤ c δ_U(a(y_κ))⁻¹ μQ(W)`.
  - `δ_U ∘ a` is multiplicative, and on the box it is at most `∏ 2^{e_i}`. Hence on `P_κ`,
    `f ≤ δ_U(a(x)) Φ(κ) ≤ 2^{∑ e_i} δ_U(a(y_κ)) Φ(κ)`.
  - `setLIntegral_le_mul_of_forall_le` bounds the integral over `P_κ` by the product of these
    two bounds, in which `δ_U(a(y_κ))` cancels. Sum over `κ` with `lintegral_iUnion_le`, and
    compare the sum over the occurring indices with the sum over all of `ℤ^ι`
    (`ENNReal.tsum_comp_le_tsum_of_injective`).

### Summation

- `tsum_pi_prod_le'`: `∑_{m : ι → β} ∏_i f_i(m_i) ≤ ∏_i ∑_n f_i(n)` in `[0, ∞]`, for a finite
  `ι` and any index type `β`. The proof is that of the published `tsum_pi_prod_le` (stated for
  `β = ℕ`): finite partial sums lie in a finite box `Fintype.piFinset`, where the sum of products
  is the product of sums.
- `tsum_int_inv_one_add_abs_sq_ne_top`: `∑_{n ∈ ℤ} (1 + |n|)⁻² < ∞`. It is compared with
  Mathlib's `Real.summable_abs_int_rpow` for `n ≠ 0`, plus the single term at `0`.
- `tsum_decay_ne_top`: for `c > 0` and any `C₀`, the weights
  `max(1, c ∑_i |κ_i| - C₀)^{-2|ι|}` have finite sum over `κ ∈ ℤ^ι`. *Proof.* With
  `S = ∑_i |κ_i|` and `C₁ = max(C₀, 0)` one has
  `max(1, c S - C₀) ≥ K₀ (1 + S)` with `K₀ = min(1, c) / (2(1 + C₁)) > 0`. Since
  `1 + |κ_i| ≤ 1 + S` for each `i`, `(1 + S)^{-2|ι|} ≤ ∏_i (1 + |κ_i|)^{-2}`. The sum of the
  products is bounded by `tsum_pi_prod_le'` and `tsum_int_inv_one_add_abs_sq_ne_top`.

The module uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
