# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The FLT declaration `AddSubgroup.inertia_mono` (`I ≤ J → I.inertia G ≤ J.inertia G` for additive subgroups) is removed, because the pinned Mathlib now declares the same lemma under the same name (with `G` explicit); the then empty `namespace AddSubgroup … end AddSubgroup` block with its `variable` line remains.
- The proof of `Ideal.inertia_mono` calls Mathlib's `AddSubgroup.inertia_mono G …` (with the explicit argument `G`) instead of FLT's `AddSubgroup.inertia_mono …`.
- `IsLocalRing.lowerRamificationGroup` is an abbreviation for the existing
  `Langlands.Ramification.lowerGroup`, imported from
  `Langlands.LocalFactor.Ramification.Filtration`. Both unfold to
  `((maximalIdeal R) ^ (i + 1)).inertia G` with the same parameters.
  `lowerRamificationGroup_zero_eq_inertia` reuses the existing
  `Langlands.Ramification.lowerGroup_zero` proof. The port keeps its source
  API name while sharing the Library construction.
- Apart from these patches the declarations, statements and proofs are the FLT text.

## Content

Lower ramification groups of a group acting on a local ring (FLT's staging file for Mathlib).

- Inertia subgroups of ideals (namespace `Ideal`, for a group `G` acting on a commutative ring `R` by a
  `MulSemiringAction`): `Ideal.inertia_mono` (`I ≤ J → I.inertia G ≤ J.inertia G`), `Ideal.inertia_top`
  (`(⊤ : Ideal R).inertia G = ⊤`) and `Ideal.inertia_normal_of_forall_smul_eq` (the inertia subgroup of an
  ideal with `g • I = I` for all `g` is normal).
- For a local ring `R` with a `MulSemiringAction` of a group `G` (namespace `IsLocalRing`):
  `pointwise_smul_maximalIdeal` and `pointwise_smul_maximalIdeal_pow` (`g • 𝔪 = 𝔪` and `g • 𝔪ⁿ = 𝔪ⁿ`), and
  the definition `lowerRamificationGroup R G i := ((maximalIdeal R) ^ (i + 1)).inertia G`, so that
  `σ ∈ lowerRamificationGroup R G i ↔ ∀ x : R, σ • x - x ∈ (maximalIdeal R) ^ (i + 1)`
  (`mem_lowerRamificationGroup`, proved by `Iff.rfl`). The index `i : ℕ` is the classical lower index: the
  group is Serre's `G_i` (Local Fields, IV §1), whose elements move every element by at least `i + 1` in
  valuation; there is no group of index `-1`.
- Properties: `lowerRamificationGroup_antitone`, the instance `lowerRamificationGroup_normal`,
  `lowerRamificationGroup_zero_eq_ker` (`G_0` is the kernel of the action on the residue field),
  `lowerRamificationGroup_zero_eq_inertia` (`G_0` is the inertia subgroup of `𝔪`), `lowerRamificationGroup_le_zero`,
  `iInf_lowerRamificationGroup_le_ker_toRingAut` (if `⨅ n, 𝔪ⁿ = ⊥`, the intersection of all `G_i` acts
  trivially on `R`) and `iInf_lowerRamificationGroup_eq_bot` (the same with `FaithfulSMul G R`: the intersection
  is `⊥`).
- For a field extension `L/K` and a valuation subring `A` of `L` (namespace `ValuationSubring`):
  `A.lowerRamificationGroup K i`, the lower group of the decomposition subgroup `A.decompositionSubgroup K` acting
  on `A`, with `mem_lowerRamificationGroup`, `lowerRamificationGroup_antitone`, the instance
  `lowerRamificationGroup_normal`, `lowerRamificationGroup_zero` (`= A.inertiaSubgroup K`) and
  `lowerRamificationGroup_le_inertiaSubgroup`.

Section `Gates` contains 3 `example` checks of the definitions. The file ends with 7 `#guard_msgs in #print axioms` checks (kept from FLT), for `IsLocalRing.lowerRamificationGroup`, `IsLocalRing.lowerRamificationGroup_antitone`, `IsLocalRing.lowerRamificationGroup_normal`, `IsLocalRing.lowerRamificationGroup_zero_eq_ker`, `IsLocalRing.iInf_lowerRamificationGroup_eq_bot`, `ValuationSubring.lowerRamificationGroup_zero`, `ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup`; each fails unless the printed axiom list is the expected one, a subset of `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Ideal.inertia_mono`
- theorem `Ideal.inertia_top`
- theorem `Ideal.inertia_normal_of_forall_smul_eq`
- theorem `IsLocalRing.pointwise_smul_maximalIdeal`
- theorem `IsLocalRing.pointwise_smul_maximalIdeal_pow`
- abbrev `IsLocalRing.lowerRamificationGroup`
- theorem `IsLocalRing.mem_lowerRamificationGroup`
- theorem `IsLocalRing.lowerRamificationGroup_antitone`
- instance `IsLocalRing.lowerRamificationGroup_normal`
- theorem `IsLocalRing.lowerRamificationGroup_zero_eq_ker`
- theorem `IsLocalRing.lowerRamificationGroup_zero_eq_inertia`
- theorem `IsLocalRing.lowerRamificationGroup_le_zero`
- theorem `IsLocalRing.iInf_lowerRamificationGroup_le_ker_toRingAut`
- theorem `IsLocalRing.iInf_lowerRamificationGroup_eq_bot`
- def `ValuationSubring.lowerRamificationGroup`
- theorem `ValuationSubring.mem_lowerRamificationGroup`
- theorem `ValuationSubring.lowerRamificationGroup_antitone`
- instance `ValuationSubring.lowerRamificationGroup_normal`
- theorem `ValuationSubring.lowerRamificationGroup_zero`
- theorem `ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`, `Langlands.LocalFactor.Ramification.Filtration`.
