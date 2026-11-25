# Herbrand's tower law for the rational Herbrand functions

`Langlands.LocalFactor.Ramification.Herbrand.RationalQuotient`. Let a finite group `G` act on a
local ring `R`, let `H` be a normal subgroup and let `G ⧸ H` act on a local ring `S` (in the
applications `S = FixedPoints.subring R H`). Suppose that the images of the lower groups of `G`
are the lower groups of the quotient in Herbrand's numbering,
`G_n H / H = (G/H)_⌈φ_H(n)⌉` for every `n`, where `φ_H = herbrandPhiRat R H`. This module derives
the two consequences of Serre, *Local Fields*, IV, §3: the tower law `φ_G = φ_{G/H} ∘ φ_H` and the
compatibility of the upper numbering with quotients. The hypothesis itself is proved for
discrete valuation rings in `Herbrand/LowerQuotient.lean`.

## Statements

Name space `Langlands.Ramification`.

```lean
theorem herbrandPhiRat_eq_herbrandPhiRat_quotient_comp_of_map_lowerGroup_mk_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (lowerGroup R G n).map (QuotientGroup.mk' H) =
        lowerGroup S (G ⧸ H) ⌈herbrandPhiRat R H (n : ℚ)⌉₊)
    {u : ℚ} (hu : 0 ≤ u) :
    herbrandPhiRat R G u =
      herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H u)

theorem upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (lowerGroup R G n).map (QuotientGroup.mk' H) =
        lowerGroup S (G ⧸ H) ⌈herbrandPhiRat R H (n : ℚ)⌉₊) :
    UpperGroupRatQuotientCompat R G S H
```

The second says `(upperGroupRat R G v).map (QuotientGroup.mk' H) = upperGroupRat S (G ⧸ H) v` for all
`v ≥ 0`. Here `H` acts on `R` by restriction, so `herbrandPhiRat R H` is the Herbrand function of
`H` (that is, of the extension over the fixed field of `H`), and `φ_{G/H}` is computed from the
action on `S`.

## Proofs

Write `c(n) = ⌈φ_H(n)⌉` (`herbrandPhiRatCeil`) and call the hypothesis
`LowerHerbrandQuotientCompat`. The orders satisfy
`|G_n| = |G_n H / H| · |H_n| = |(G/H)_{c(n)}| · |H_n|` (`card_lowerGroup_map_mul_card_subgroup`,
`LowerHerbrandQuotientCompat.lowerGroupCard_quotient_mul`), since `G_n ∩ H = H_n`. On each segment
`[m, m + 1]`, `φ_H` is linear with values in `[c(m+1) - 1, c(m+1)]` (`herbrandPhiRat_mem_segment_phiCeil_succ`),
where `φ_{G/H}` is linear of slope `|(G/H)_{c(m+1)}| / |(G/H)_0|`; composing the two linear functions
and using the order formula gives the slope `|G_{m+1}| / |G_0|` of `φ_G`
(`LowerHerbrandQuotientCompat.herbrandPhiRat_comp_segment`). Induction on `m` from `φ(0) = 0`
gives equality at natural numbers and then on every segment (`herbrandPhiRat_comp_natCast`,
`herbrandPhiRatTowerCompat`).

For the upper groups, `G^v = G_n` with `n = upperGroupRatIndex R G v` the least `n` with
`v ≤ φ_G(n)`; the tower law and the divisibility `|G_j| ∣ |G_i|` for `i ≤ j`
(`lowerGroupCard_dvd_of_le`, `lowerGroupCard_dvd_sum_Icc`) show that `φ_H` maps this index into the
segment that defines the upper index of `v` for `G/H`, i.e. `⌈φ_H(n)⌉ = upperGroupRatIndex S (G ⧸ H) v`
(`ceil_herbrandPhiRat_upperGroupRatIndex`); the hypothesis at `n` then gives the image of `G^v`.

## Declarations

In the order of the file. Lemmas of the proofs are in `Langlands.Ramification.RationalQuotient`:
`herbrandPhiRatCeil`, `herbrandPhiRatCeil_eq_ceil`, `herbrandPhiRatCeil_zero` (a scoped `simp`
lemma), `LowerHerbrandQuotientCompat` (the hypothesis as a proposition), `HerbrandPhiTowerCompat`
(the conclusion as a proposition), `herbrandPhiRat_tower_zero`, `HerbrandPhiTowerCompat.natCast`,
`lowerGroupCard_dvd_of_le`, `lowerGroupCard_dvd_zero`, `lowerGroupCard_dvd_sum_Icc`,
`herbrandPhiRat_natCast_eq_cast_div`, `one_le_herbrandPhiRatCeil_succ`,
`herbrandPhiRatCeil_succ_cast_sub_one_le`, `card_lowerGroup_map_mul_card_subgroup`,
`LowerHerbrandQuotientCompat.lowerGroupCard_quotient_mul`,
`herbrandPhiRat_mem_segment_phiCeil_succ`, `LowerHerbrandQuotientCompat.herbrandPhiRat_comp_segment`,
`LowerHerbrandQuotientCompat.herbrandPhiRat_comp_natCast`,
`LowerHerbrandQuotientCompat.herbrandPhiRatTowerCompat`; then the theorem
`herbrandPhiRat_eq_herbrandPhiRat_quotient_comp_of_map_lowerGroup_mk_eq`; then
`RationalQuotient.sum_Icc_le_mul_of_herbrandPhiRat_natCast_le`,
`RationalQuotient.exists_nat_segment_increment`, `RationalQuotient.exists_nat_herbrandPsiRat_natCast`,
`RationalQuotient.ceil_herbrandPhiRat_upperGroupRatIndex`; then the theorem
`upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq`.

## Source and licence

Adapted from four files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean` | `0d8b99478d961e8d5631cb78d2eabce54ff3dc9cf36cca6e7659268086536045` |
| `P2M/Sol/S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean` | `c2e7b5e747b182df30ee2c2001f25f7e90c650c6ffa9c6f1b791ddd3d1e18ea1` |
| `Theorems/Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean` | `9874f72be193bdaa3ba15b397b574e7bcda72beb240cc31c6e95ed1c4c3b8d6b` |
| `P2M/Sol/S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean` | `293c413e0536a6efbf2909bb7d76b6af267ec284c3fc8478c7d46e9d2b2ea0b3` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files:

- Each FLT statement file and its proof file are one theorem; the two proofs are one module. The
  FLT proof name spaces `P2MW.<file>.HerbrandPort.IsLocalRing` are
  `Langlands.Ramification.RationalQuotient`; the four lemmas that both FLT proofs carried
  (`lowerRamificationCard_dvd_of_le`, `…_dvd_zero`, `…_dvd_sum_Icc`, `herbrandPhi_natCast_eq_cast_div`)
  are kept once. Names follow the Library (`IsLocalRing.herbrandPhi` is `herbrandPhiRat`, and so on;
  see `Herbrand/Rational.md`).
- The second proof erases two `simp` lemmas (`lowerGroup_subgroupOf`, `lowerGroup_map_subtype`) as
  the FLT file did; the erasure is confined to its section. The FLT file also erased the
  corresponding `ValuationSubring` lemmas, which are not ported.
- The deprecated `Set.mem_setOf_eq` is replaced by `Set.mem_ofPred_eq`; no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter IV, §3: Herbrand's theorem `G_u H/H = (G/H)_v` with
`v = φ_{L/K'}(u)` (Lemma 5, printed page 75), the transitivity `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}`
derived from it (Proposition 15, printed page 74, proved on page 75), and the compatibility
`G^v H/H = (G/H)^v` of the upper numbering (Proposition 14, printed page 74, proved on page 75).
