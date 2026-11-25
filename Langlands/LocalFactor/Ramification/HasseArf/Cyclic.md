# The Hasse–Arf theorem for a cyclic group

`Langlands.LocalFactor.Ramification.HasseArf.Cyclic`. For a cyclic group acting faithfully on a
discrete valuation ring with perfect residue field and separable residue extension over the
invariants, the lower filtration has the Hasse–Arf property: `|G_0|` divides `|G_1| + ⋯ + |G_i|` at
every break `i`, that is, `φ(i)` is an integer. `HasseArf/Abelian.lean` reduces the abelian case to
this one.

## Statement

```lean
theorem Langlands.Ramification.hasseArfChain_lowerGroup_of_isCyclic
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsCyclic G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    HasseArfChain (lowerGroup R G)
```

## Proof

Let `p` be the characteristic of the residue field.

- `p = 0`. For `s ∈ G_i`, `i ≥ 1`, and a uniformizer `ϖ`,
  `s^k ϖ - ϖ ≡ k (s ϖ - ϖ)` modulo `m^(i+2)` (`pow_smul_sub_sub_nsmul_mem`, from
  `smul_sub_mem_pow_of_mem_pow`); for `k` the order of `s`, which is a unit of `R`, this gives
  `s ϖ - ϖ ∈ m^(i+2)`, so `s ∈ G_{i+1}` (`mem_succ_of_mem_of_isUnit`). Hence there is no break
  `i ≥ 1`, and at `i = 0` the property is trivial.
- `p` prime. Then `p ∈ m`, `G_1` is a `p`-group (`isPGroup_lowerGroup_one`), `[G_0 : G_1]` is prime to
  `p` (`exists_monoidHom_lowerGroup_zero_residueField_units`), the breaks `i ≥ 1` are multiples of
  `[G_0 : G_1]` because `G` is commutative (`relIndex_dvd_of_lowerGroup_ne_succ_of_commute`), and the
  depths satisfy Sen's congruences (`ramificationDepth_pow_prime_pow_modEq_of_mem_lowerGroup_one`);
  `hasseArfChain_of_isCyclic_of_dvd_of_modEq` concludes.

## Declarations

In the order of the file, in `Langlands.Ramification.HasseArf.Cyclic`:
`pow_add_eq_pow_of_mul_eq_zero`, `smul_sub_mem_pow_of_mem_pow`, `pow_smul_sub_sub_nsmul_mem`,
`mem_succ_of_mem_of_isUnit`; then `hasseArfChain_lowerGroup_of_isCyclic` in `Langlands.Ramification`.

## Source and licence

Adapted from two files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean` | `af69d93af0acf82ee834f7374374fc082698299ed3d660e261f07da45208c4df` |
| `P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean` | `7727de32744112ee1ae031b4aea44a48d6e749f52d943703221246a155ee3965` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files: the statement and its proof are one module; the FLT proof name spaces
`P2MW.<file>.Ws45.HATame` and `P2MW.<file>.HasseArfCyc` are `Langlands.Ramification.HasseArf.Cyclic`;
the four lemmas of `Ws45.HATame` (`residue_smul_of_mem_zero`, `exists_invariant_sub_mem`,
`smul_sub_dvd_smul_sub_of_mem_lowerRamificationGroup_zero`,
`mem_lowerRamificationGroup_iff_smul_uniformizer_sub_mem_pow`) were copies of lemmas of the FLT proof
of the tame character and are those of `LowerGroupQuotients.lean`;
`IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic` is
`Langlands.Ramification.hasseArfChain_lowerGroup_of_isCyclic`, stated on `lowerGroup`; no options
are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter V, §7, Theorem 1, printed page 93 (the Hasse–Arf
theorem), and Chapter IV, §2 (`G_0/G_1` and `G_1`): Proposition 7 and Corollaries 1–3, printed
page 67 (`G_0/G_1` cyclic of order prime to the residue characteristic, `G_1 = {1}` in residue
characteristic zero, `G_1` a `p`-group), and Corollary 2 to Proposition 9, printed page 70 (for
abelian `G` the breaks `i ≥ 1` are multiples of the order of `G_0/G_1`).
