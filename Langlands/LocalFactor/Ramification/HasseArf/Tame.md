# Breaks of an abelian inertia group are divisible by the tame index

`Langlands.LocalFactor.Ramification.HasseArf.Tame`. The tame half of the Hasse–Arf theorem for a
cyclic group: if `G_0` is commutative, every break `i ≥ 1` of the lower filtration is a multiple of
`[G_0 : G_1]`. With the congruences of `HasseArf/Congruence.lean` it gives the cyclic case in
`HasseArf/Cyclic.lean`.

## Statement

```lean
theorem Langlands.Ramification.relIndex_dvd_of_lowerGroup_ne_succ_of_commute
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hcomm : ∀ s ∈ lowerGroup R G 0, ∀ t ∈ lowerGroup R G 0, Commute s t)
    {i : ℕ} (hi : 1 ≤ i)
    (hjump : lowerGroup R G i ≠ lowerGroup R G (i + 1)) :
    (lowerGroup R G 1).relIndex (lowerGroup R G 0) ∣ i
```

## Proof

Fix a uniformizer `ϖ` and write `σ ϖ = u_σ ϖ` (`LowerGroupQuotients.unifUnit`). Take `τ ∈ G_i` not in
`G_{i+1}`; then `u_τ = 1 + c ϖ^i` with `c` a unit (otherwise `τ ∈ G_{i+1}` by
`mem_lowerGroup_of_smul_uniformizer_unit_sub_one_mem_pow`). For `s ∈ G_0` commuting with `τ`, the
two expressions `(sτ) ϖ = u_s s(u_τ) ϖ` and `(τs) ϖ = u_τ τ(u_s) ϖ` agree; since `τ(u_s) ≡ u_s` modulo
`m^{i+1}` and `s(c) ≡ c` modulo `m`, this gives `c u_s ϖ^i (u_s^i - 1) ∈ m^{i+1}`, hence
`u_s^i ≡ 1` modulo `m` (`pow_sub_one_mem_maximalIdeal_of_commute`). Now `G_0/G_1` is cyclic
(`exists_monoidHom_lowerGroup_zero_residueField_units`); for a generator `g`, `u_{g^i} ≡ u_g^i ≡ 1`
(`unifUnit_pow_sub_pow_mem`), so `g^i ∈ G_1` and the order `[G_0 : G_1]` of `g` divides `i`.

## Declarations

In the order of the file, in `Langlands.Ramification.HasseArf.Tame`: `smul_sub_mem_maximalIdeal`,
`varpi_mem`, `unifUnit_pow_sub_pow_mem`, `pow_sub_one_mem_maximalIdeal_of_commute`; then
`relIndex_dvd_of_lowerGroup_ne_succ_of_commute` in `Langlands.Ramification`.

## Source and licence

Adapted from two files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean` | `245e2e7e582aaddcec47cbcc58b22a27e0a608625ec0c1221ffefd86dc39ecff` |
| `P2M/Sol/S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean` | `58fceddfe15f9216e0d88c3845d14a19bc08eab966f85f25c34e723017e323d3` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files: the statement and its proof are one module; the FLT proof name space
`P2MW.<file>.Ws45.HATame` is `Langlands.Ramification.HasseArf.Tame`. Eight of its lemmas were
copies of lemmas of the FLT proof of the tame character (`residue_smul_of_mem_zero`,
`exists_invariant_sub_mem`, `smul_sub_dvd_smul_sub_of_mem_lowerRamificationGroup_zero`, its copy
`core_fin`, `mem_lowerRamificationGroup_iff_smul_uniformizer_sub_mem_pow`, and the unit `uu` with
`uu_one`, `uu_spec`, which is that proof's `unifUnit`); the ones of `LowerGroupQuotients.lean` are
used, and `uu_pow_sub_pow_mem` is `unifUnit_pow_sub_pow_mem`. Upstream's
`IsDiscreteValuationRing.relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute` is
`Langlands.Ramification.relIndex_dvd_of_lowerGroup_ne_succ_of_commute`; statements are on
`lowerGroup`; the FLT statement file erased two instances for its statement; no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter IV, §2, Proposition 9 and Corollary 1, printed page
69, and Corollary 2, printed page 70: for `s ∈ G_0` and `t ∈ G_i`, `i ≥ 1`,
`θ_i(s t s^{-1}) = θ_0(s)^i θ_i(t)`; if `G_0` is abelian, the breaks `i ≥ 1` are therefore multiples
of the order of `G_0/G_1`. Serre states Corollary 2 for abelian `G`; its proof uses only that the
elements of `G_0` commute.
