# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Lower ramification groups of subgroups (namespace `IsLocalRing`; `R` local with a `MulSemiringAction` of `G`; a
subgroup `H` acts on `R` by restriction).

- `lowerRamificationGroup_comap_of_forall_smul_eq`: for a hom `f : H →* G` with `f h • x = h • x`,
  `lowerRamificationGroup R H i = (lowerRamificationGroup R G i).comap f`.
- For `H : Subgroup G`: `mem_lowerRamificationGroup_subgroup` (`σ ∈ H_i ↔ (σ : G) ∈ G_i`),
  `lowerRamificationGroup_subgroupOf` (`G_i.subgroupOf H = H_i`), `lowerRamificationGroup_map_subtype`
  (`H_i.map H.subtype = G_i ⊓ H`, Serre's `H_i = G_i ∩ H`, Local Fields IV §1 Proposition 2) and its variant
  `lowerRamificationGroup_map_subtype'` (`= H ⊓ G_i`), `lowerRamificationGroup_subgroup_eq_top_iff`
  (`H_i = ⊤ ↔ H ≤ G_i`), and for `H ≤ K`: `lowerRamificationGroup_comap_inclusion` and
  `lowerRamificationGroup_map_subtype_le_map_subtype`.
- `ValuationSubring` versions for subgroups of the decomposition subgroup: `lowerRamificationGroup_subgroupOf`,
  `mem_lowerRamificationGroup_subgroup`, `lowerRamificationGroup_map_subtype` and
  `lowerRamificationGroup_zero_map_subtype` (`H_0` maps onto `A.inertiaSubgroup K ⊓ H`).

Section `Gates` contains 6 `example` checks of the definitions. The file ends with 8 `#guard_msgs in #print axioms` checks (kept from FLT), for `IsLocalRing.lowerRamificationGroup_comap_of_forall_smul_eq`, `IsLocalRing.lowerRamificationGroup_subgroupOf`, `IsLocalRing.lowerRamificationGroup_map_subtype`, `IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff`, `IsLocalRing.lowerRamificationGroup_comap_inclusion`, `ValuationSubring.lowerRamificationGroup_subgroupOf`, `ValuationSubring.lowerRamificationGroup_map_subtype`, `ValuationSubring.lowerRamificationGroup_zero_map_subtype`; each fails unless the printed axiom list is the expected one, a subset of `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `IsLocalRing.lowerRamificationGroup_comap_of_forall_smul_eq`
- theorem `IsLocalRing.mem_lowerRamificationGroup_subgroup`
- theorem `IsLocalRing.lowerRamificationGroup_subgroupOf`
- theorem `IsLocalRing.lowerRamificationGroup_map_subtype`
- theorem `IsLocalRing.lowerRamificationGroup_map_subtype'`
- theorem `IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff`
- theorem `IsLocalRing.lowerRamificationGroup_comap_inclusion`
- theorem `IsLocalRing.lowerRamificationGroup_map_subtype_le_map_subtype`
- theorem `ValuationSubring.lowerRamificationGroup_subgroupOf`
- theorem `ValuationSubring.mem_lowerRamificationGroup_subgroup`
- theorem `ValuationSubring.lowerRamificationGroup_map_subtype`
- theorem `ValuationSubring.lowerRamificationGroup_zero_map_subtype`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup`.
Other imports: `Mathlib`.
