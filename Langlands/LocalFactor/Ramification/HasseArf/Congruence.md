# The depth congruence for powers of a wild automorphism

`Langlands.LocalFactor.Ramification.HasseArf.Congruence`. Sen's congruence: for a wild automorphism
`σ` of a discrete valuation ring with perfect residue field of characteristic `p`, the depths of the
`p`-power iterates satisfy `i(σ^(p^(n-1))) ≡ i(σ^(p^n))` modulo `p^n` as long as `σ^(p^n) ≠ 1`. It is
the wild input of the Hasse–Arf theorem for cyclic groups (`HasseArf/Counting.lean`,
`HasseArf/Cyclic.lean`). This file holds the longest proof of the Hasse–Arf development; it is a
module of its own.

## Statement

```lean
theorem Langlands.Ramification.ramificationDepth_pow_prime_pow_modEq_of_mem_lowerGroup_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    [PerfectField (IsLocalRing.ResidueField R)]
    {σ : G} (hσ : σ ∈ lowerGroup R G 1)
    {n : ℕ} (hn : 1 ≤ n) (hσn : σ ^ p ^ n ≠ 1) :
    (ramificationDepth R G (σ ^ p ^ (n - 1))).toNat ≡
      (ramificationDepth R G (σ ^ p ^ n)).toNat [MOD p ^ n]
```

`ramificationDepth` is the depth `i_G` of `Depth.lean`; `.toNat` is harmless since the depths
involved are finite (`σ^(p^j) ≠ 1` for `j ≤ n`).

## Proof

Strong induction on `n`. Write `e_j = i(σ^(p^j))`; the `e_j` increase with `j`, and by induction
`p^(j+1)` divides `e_(j+1) - e_j` for `j + 1 < n`. Suppose `p^n` does not divide `D = e_n - e_(n-1)` and
put `a = (p - 1) D`, so that `v_p(p a) = n`.

1. *Depth of powers.* `i(σ^k) = i(σ^(p^(v_p(k))))` for `k ≠ 0` (`depth_pow_eq`, from
   `ramificationDepth_pow_eq_of_mem_lowerGroup_one_of_not_dvd`: powers prime to `p` do not change the
   depth of an element of `G_1`); hence `i((σ^p)^a) = e_n`.
2. *A test element.* There is `α` with `v(α) = a` and `v(σ^p α - α) = a - 1 + e_n =: V`
   (`exists_addVal_eq_and_addVal_smul_sub_eq`: take a product of conjugates of a uniformizer). Put
   `β = ∑_{t < p} σ^t α`; then `β ∈ m^(a+1)` (`sum_range_smul_mem_pow_succ`, using `p ∈ m`) and
   `σ β - β = σ^p α - α`, of valuation `V`.
3. *Digits.* With elements `γ_k` of valuation `k` and `v(σ γ_k - γ_k) = k - 1 + e_(v_p(k))`, expand
   `β ≡ ∑_{a < k ≤ V} θ_k γ_k` modulo `m^(V+1)` with digits `θ_k` that are `0` or units and are almost
   fixed by `σ` (`exists_digits_sub_sum_mem_pow_of_prime_mem`; the residue field being perfect,
   `exists_eq_pow_add_mul` and `smul_sub_mem_sup_pow` give the digits, `exists_digit`,
   `exists_digits_Ico`).
4. *Contradiction.* Modulo `m^(V+1)`, `σ β - β` is `∑ θ_k (σ γ_k - γ_k)` over the `k` with `θ_k ≠ 0` and
   `p^n ∤ k`. The valuations `k - 1 + e_(v_p(k))` of these terms are pairwise distinct (`eq_of_w_eq`,
   from the divisibilities of the `e_j`), so the valuation of the sum is their minimum
   (`exists_min_addVal_sum_eq`), and none of them equals `V` (`w_ne_V`, from `p^n ∤ D`). So
   `v(σ β - β) ≠ V`, a contradiction.

## Declarations

In the order of the file, in `Langlands.Ramification.HasseArf.Congruence` (sections in brackets):
[ResidueLifts] `exists_eq_pow_add_mul`, `smul_sub_mem_sup_pow`; [DivisibilityOnInertia]
`smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero_of_prime_mem`; [DepthOnUniformizer]
`ramificationDepth_eq_addVal`, `isUnit_natCast_of_not_dvd`; [PowersPrimeToP]
`ramificationDepth_pow_eq_of_mem_lowerGroup_one_of_not_dvd`,
`exists_sub_mem_maximalIdeal_and_smul_sub_mem_pow_of_prime_mem`; [ValuationOfProducts]
`addVal_prod_smul_uniformizer`, `addVal_prod_pow_smul_uniformizer`; [ElementOfGivenValuation]
`exists_addVal_eq_and_addVal_smul_sub_eq`; [Digits] `exists_unit_mul_pow_of_addVal_eq`,
`exists_digit`, `exists_digits_Ico`; [DigitExpansion] `exists_digits_sub_sum_mem_pow_of_prime_mem`;
[Estimates] `smul_sub_mem_pow_add_of_mem_lowerGroup`, `addVal_add_eq_of_lt`, `smul_sum_range_sub`,
`sum_range_smul_mem_pow_succ`, `coe_toNat_ramificationDepth`, `mem_iff_succ_le_toNat`;
[DepthOfPowers] `depth_pow_eq`; [DistinctValuations] `exists_min_addVal_sum_eq`, `eq_of_w_eq`,
`w_ne_V`; then `ramificationDepth_pow_prime_pow_modEq_of_mem_lowerGroup_one` in
`Langlands.Ramification`.

## Source and licence

Adapted from two files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.lean` | `e89f1dca18010e48baf6980277ffc9a2c372cd97fd8cc03c15ba7869e8e4706d` |
| `P2M/Sol/S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.lean` | `18ae866a724a32746a92bfee2315794d9ef17688b6ea1024c44e58656549dd37` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files:

- The statement and its proof are one module. The FLT proof used the name spaces
  `IsDiscreteValuationRing.CorePSol`, `.Sen1Sol`, `.Sen3Sol`, `Ws45.Digits`, `Ws45.Sen2` inside its
  proof name space and declared further lemmas as `IsDiscreteValuationRing.…` there; all are in
  `Langlands.Ramification.HasseArf.Congruence`, one section per FLT block, with the section names
  above. The FLT `export _root_.IsDiscreteValuationRing (…)` lines are `open IsDiscreteValuationRing`.
- The FLT file proved the same lemma twice (`Sen1Sol.ramificationDepth_eq_addVal` and
  `Sen3Sol.depth_eq_addVal`); it is kept once, as `ramificationDepth_eq_addVal`.
- Statements are on `lowerGroup`; upstream's
  `IsDiscreteValuationRing.ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one`
  is `Langlands.Ramification.ramificationDepth_pow_prime_pow_modEq_of_mem_lowerGroup_one`.
- Deprecated names are replaced (`ENat.coe_ne_top`, `ENat.coe_toNat`, `ENat.top_ne_coe` by
  `ENat.natCast_ne_top`, `ENat.natCast_toNat`, `ENat.top_ne_natCast`). No options are set: the
  proof compiles within Lean's default limits, so it is not split further.

## Literature

S. Sen, *On automorphisms of local fields*, Ann. of Math. 90 (1969), 33–46, Main theorem,
Theorem 1, printed pages 34–35, proved with Lemmas 1–3 on printed pages 35–36: the congruence
`i(σ^(p^n)) ≡ i(σ^(p^(n-1)))` modulo `p^n`. Sen states it for a wildly ramified automorphism of a
field complete under a discrete valuation with perfect residue field, with `i(σ) = Ord (σ - 1)π/π`
(one less than `ramificationDepth`) and with the congruence taken to hold when a side is `∞`; here
`R` need not be complete, and `σ^(p^n) ≠ 1` is assumed instead. Serre, *Local Fields*, GTM 67
(1979), Chapter IV, §2, Proposition 7 and Corollary 3, printed page 67, for the lower groups `G_i`
and `G_1` as a `p`-group, and Chapter V, §7, Theorem 1, printed page 93, for the Hasse–Arf theorem
that this congruence serves.
