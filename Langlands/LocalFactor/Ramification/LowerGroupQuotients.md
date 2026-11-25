# The quotients of consecutive lower ramification groups

`Langlands.LocalFactor.Ramification.LowerGroupQuotients`. Serre's description of `G_0/G_1` and of
`G_1` for a finite group acting on a discrete valuation ring: `G_0/G_1` embeds into the units of the
residue field, hence is cyclic of order prime to the residue characteristic, and `G_1` is a
`p`-group, `p` the residue characteristic. These are the tame and wild inputs of the Hasse–Arf
theorem (`HasseArf/`).

## Statements

Name space `Langlands.Ramification`.

```lean
theorem exists_monoidHom_lowerGroup_zero_residueField_units
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)] :
    (∃ θ : ↥(lowerGroup R G 0) →* (IsLocalRing.ResidueField R)ˣ,
        θ.ker = (lowerGroup R G 1).subgroupOf (lowerGroup R G 0)) ∧
    IsCyclic (↥(lowerGroup R G 0) ⧸ (lowerGroup R G 1).subgroupOf (lowerGroup R G 0)) ∧
    (∀ p : ℕ, p.Prime → (p : R) ∈ IsLocalRing.maximalIdeal R →
        ¬ p ∣ (lowerGroup R G 1).relIndex (lowerGroup R G 0))

theorem pow_mem_lowerGroup_succ {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R]
    {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) {i : ℕ} (hi : 1 ≤ i) {σ : G}
    (hσ : σ ∈ lowerGroup R G i) :
    σ ^ p ∈ lowerGroup R G (i + 1)

theorem isPGroup_lowerGroup_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hsep : ⨅ n, IsLocalRing.maximalIdeal R ^ n = ⊥) :
    IsPGroup p (lowerGroup R G 1)
```

The first does not assume the action faithful. In the last, `p` is any natural number in the
maximal ideal; for a prime residue characteristic it is the statement that `G_1` is a `p`-group.

## Proofs

*The character `θ₀`.* For a uniformizer `ϖ` and `σ ∈ G`, `σ ϖ = u_σ ϖ` with a unit `u_σ`
(`unifUnit`, from `Uniformizer.lean`), and `u_{στ} = u_σ σ(u_τ)`. For `σ ∈ G_0`, `σ` acts trivially
on the residue field, so `θ₀(σ) = u_σ mod m` is a homomorphism `G_0 → k^×` (`theta0`). Its kernel is
`G_1`. First, every element of `R` is congruent modulo `m` to an element fixed by `G_0`
(`exists_invariant_sub_mem`): the polynomial `∏_{h ∈ G_0} (X - h r)` has invariant coefficients and
reduces to `(X - r̄)^{|G_0|}`, so `r̄` is purely inseparable over the residue field of the
invariants, and as `k` is perfect it lies in that field. Hence `σ x - x` is a multiple of
`σ ϖ - ϖ` for `σ ∈ G_0` (write `x` as an invariant plus a multiple of `ϖ` and repeat;
`smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero`)
(`smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero`), and `σ ∈ G_i` exactly when `σ ϖ - ϖ ∈ m^(i+1)`
(`mem_lowerGroup_iff_smul_uniformizer_sub_mem_pow`), i.e. `u_σ ≡ 1` modulo `m^i`. The image of
`θ₀` is a finite subgroup of `k^×`, hence cyclic, and of order prime to `p` when `p = 0` in `k`
(`not_dvd_card_of_charP`: `x^p = 1` forces `x = 1` in characteristic `p`).

*Powers.* For `σ ∈ G_i` and `y ∈ m^j`, `σ y - y ∈ m^{i+j}`
(`smul_sub_mem_maximalIdeal_pow_add_of_mem_lowerGroup`). With `y = σ x - x ∈ m^{i+1}` this gives
`σ^n y - y ∈ m^{2i+1} ⊆ m^{i+2}` for `i ≥ 1`, and by induction `σ^n x - x ≡ n y` modulo `m^{i+2}`. For
`n = p` the right side `p y` lies in `m · m^{i+1}`, so `σ^p ∈ G_{i+1}`. Iterating, `σ^{p^k} ∈ G_{k+1}` for `σ ∈ G_1`, and the lower groups are trivial from
some index on (`exists_lowerGroup_eq_bot_of_iInf_eq_bot`), so every element of `G_1` has order a
power of `p`.

## Declarations

In the order of the file, in `Langlands.Ramification.LowerGroupQuotients`: `unifUnit`,
`unifUnit_spec`, `unifUnit_one`, `coe_unifUnit_mul`, `residue_smul_of_mem_zero`, `theta0`,
`coe_theta0_apply`, `mem_ker_theta0_iff`, `exists_invariant_sub_mem`,
`smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero`, `mem_lowerGroup_iff_smul_uniformizer_sub_mem_pow`,
`ker_theta0`, `not_dvd_card_of_charP`; `exists_monoidHom_lowerGroup_zero_residueField_units` in
`Langlands.Ramification`; `LowerGroupQuotients.smul_mem_maximalIdeal_pow_of_mem`,
`LowerGroupQuotients.smul_sub_mem_maximalIdeal_pow_add_of_mem_lowerGroup`; then
`pow_mem_lowerGroup_succ` and `isPGroup_lowerGroup_one`. The lemmas `exists_invariant_sub_mem`,
`smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero`, `mem_lowerGroup_iff_smul_uniformizer_sub_mem_pow`,
`residue_smul_of_mem_zero`, `unifUnit` and its two lemmas are also used by `HasseArf/Tame.lean` and
`HasseArf/Cyclic.lean`, whose FLT proofs carried copies of them.

## Source and licence

Adapted from six files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean` | `56d5275177b8d8581079e337d150d0239b5360f83a161df0e818de85b3fc2ff7` |
| `P2M/Sol/S_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean` | `8a3ba1fe108d7ba80acf95a63162749f86bc0228a026c8327351b0eaf581b6b6` |
| `Theorems/Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean` | `a9dd9b5d64d65620f82fcc3897d344a9d313852469ddaad95a0db23eda4bb346` |
| `P2M/Sol/S_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean` | `22f8167a337b90e4fbafdf96408bdc660ab65936aa3304af072e6be9d0603079` |
| `Theorems/Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean` | `219f5a52bc303f91f395e1abfce324f37081848e3650b39c906456e9177570ce` |
| `P2M/Sol/S_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean` | `2b26bd99590e32f3cd41a4fec371bc5af7955f97aaa6db2f3301e5554eaa26b8` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files: the six files are one module; the FLT proof name spaces
`P2MW.<file>.HasseArfTheta0` and `P2MW.<file>.IsLocalRing` are
`Langlands.Ramification.LowerGroupQuotients`; statements are on `lowerGroup`; upstream's
`IsDiscreteValuationRing.exists_monoidHom_lowerRamificationGroup_zero_residueField_units`,
`IsLocalRing.pow_mem_lowerRamificationGroup_succ` and `IsLocalRing.isPGroup_lowerRamificationGroup_one`
are `Langlands.Ramification.exists_monoidHom_lowerGroup_zero_residueField_units`,
`pow_mem_lowerGroup_succ` and `isPGroup_lowerGroup_one`. The FLT statement file of the first theorem
erased the instances `isLocalRing_fixedSubring` and `isLocalHom_fixedSubring_subtype`; its statement
is definitionally equal to the one here. Deprecated names are replaced (`MonoidHom.coe_coe` by
`MonoidHom.coe_ofClass`, `if_neg` by `ite_eq_right`); no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter IV, §2: the injection `θ₀ : G_0/G_1 → k^×`, the
corollaries that `G_0/G_1` is cyclic of order prime to the characteristic of `k` and that `G_1` is
a `p`-group, and the injections `θ_i : G_i/G_{i+1} → U^i/U^{i+1}` (Proposition 7 and Corollaries 1
and 3, printed page 67, with Propositions 5 and 6, printed page 66). Serre needs only a separable
residue extension; the first theorem here assumes the residue field perfect.
