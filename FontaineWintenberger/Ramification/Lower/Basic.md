# Lower ramification groups

Module `FontaineWintenberger.Ramification.Lower.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file defines the lower ramification groups of a group acting on a commutative ring, relative to an ideal, specializes them to discrete valuation rings and to decomposition groups of valuation subrings, and introduces the order function and real lower numbering.

## Definitions

- `lowerRamificationGroup G I n`, for `G` acting on `R` by ring automorphisms, an ideal `I` and `n : ℤ`: the inertia subgroup `(I ^ (n + 1).toNat).inertia G`, that is, the `g` with `g • x − x ∈ I ^ (n + 1)` for all `x`. For `n ≤ −1` it is the whole group.
- `ramificationOrder G g : ℕ∞`, for `R` a discrete valuation ring: the infimum over `x ∈ R` of `addVal R (g • x − x)`.
- `lowerRamificationGroupReal G I t`, for real `t`: `lowerRamificationGroup G I ⌈t⌉`.
- `ValuationSubring.lowerRamificationGroupInt K A n`, `ValuationSubring.ramificationOrder K A g`: the same for `A.decompositionSubgroup K` acting on a valuation subring `A` of `L`. The lemmas about the first are `ValuationSubring.mem_lowerRamificationGroupInt_iff`, `lowerRamificationGroupInt_neg_one`, `lowerRamificationGroupInt_zero` (it is `A.inertiaSubgroup K` at `0`), `lowerRamificationGroupInt_antitone`, `lowerRamificationGroupInt_normal` (an instance), `mem_lowerRamificationGroupInt_iff_addVal`, `mem_lowerRamificationGroupInt_iff_le_order`, `lowerRamificationGroupInt_eventually_eq_bot` and `mem_lowerRamificationGroupInt_iff_normalizedValuation`.

## Results

- The groups are antitone in `n`, equal `I.inertia G` at `0`, and are compatible with passing to a subgroup.
- `lowerRamificationGroup_normal`: normality when `G` preserves `I`; this holds for the maximal ideal of a local ring (`smul_maximalIdeal`; an instance).
- `lowerRamificationGroup_zero_eq_ker_residue`: for a local ring, the zeroth group is the kernel of the action on the residue field.
- `mem_maximalIdeal_pow_iff_addVal`, `addVal_smul`: in a discrete valuation ring, `x ∈ 𝔪^n` iff `n ≤ addVal R x`, and automorphisms preserve `addVal`.
- `mem_lowerRamificationGroup_iff_le_order`: `g ∈ G_n` iff `(n + 1).toNat ≤ ramificationOrder G g`.
- The order is invariant under inversion and conjugation, satisfies `min (i g) (i h) ≤ i (g * h)` with equality when `i g ≠ i h`, and, for a faithful action, is `⊤` only for `g = 1` (`ramificationOrder_eq_top_iff`).
- `lowerRamificationGroup_eventually_eq_bot`, `lowerRamificationGroupReal_eventually_eq_bot`: for a finite group acting faithfully, the lower groups are trivial for large index.
- `mem_lowerRamificationGroupReal_iff_le_order`: `g ∈ G_t` iff `t + 1 ≤ ramificationOrder G g` (compared in `ℝ≥0∞`).
- For a valuation subring `A` that is a discrete valuation ring: the adic valuation of its maximal ideal on `L` has valuation ring `A`, is preserved by the decomposition group, and describes the lower groups.

Two instances on `A.decompositionSubgroup K` are declared: a scalar action on `A` with raised priority, and its faithfulness.

## What to watch for

- These are the library's own definitions, built on Mathlib's `Ideal.inertia`; nothing is assumed on the residue field.
- `ramificationOrder` is unshifted and is an infimum over the whole ring, not defined through a generator.
- The real numbering is by ceiling: `G_t = G_⌈t⌉`.
- No completeness is assumed.

## References

Serre, *Local Fields*, Chapter IV, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Basic.lean` (SHA-256 of the source file `11ed87905d70abafba7442de830cb997fb6a7aa5706bdf479c895f420a7339ea`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
- The ten declarations of the namespace `ValuationSubring` about the lower group carry the suffix `Int` after `lowerRamificationGroup`, because the Library declares the same full names for its own lower groups of a valuation subring (with natural index). Names in the source and in the copy: `ValuationSubring.lowerRamificationGroup` → `ValuationSubring.lowerRamificationGroupInt`; `mem_lowerRamificationGroup_iff` → `mem_lowerRamificationGroupInt_iff`; `lowerRamificationGroup_neg_one` → `lowerRamificationGroupInt_neg_one`; `lowerRamificationGroup_zero` → `lowerRamificationGroupInt_zero`; `lowerRamificationGroup_antitone` → `lowerRamificationGroupInt_antitone`; `lowerRamificationGroup_normal` → `lowerRamificationGroupInt_normal`; `mem_lowerRamificationGroup_iff_addVal` → `mem_lowerRamificationGroupInt_iff_addVal`; `mem_lowerRamificationGroup_iff_le_order` → `mem_lowerRamificationGroupInt_iff_le_order`; `lowerRamificationGroup_eventually_eq_bot` → `lowerRamificationGroupInt_eventually_eq_bot`; `mem_lowerRamificationGroup_iff_normalizedValuation` → `mem_lowerRamificationGroupInt_iff_normalizedValuation` (all in `ValuationSubring`). The declarations of the same short names in the namespace `FontaineWintenberger` keep their names. No statement or proof is otherwise changed.
