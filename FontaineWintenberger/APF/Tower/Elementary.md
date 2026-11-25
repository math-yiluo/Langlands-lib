# Ramification bounds and strictness along a tower of jumps

Module `FontaineWintenberger.APF.Tower.Elementary`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a complete discretely valued field `K` and a separable extension `L/K`, the file computes the first ramification bound `apfRamificationBound K L` and the strictness constant `apfStrictnessConstant K L` from an abstract description of the jumps: a sequence `b n` of upper parameters and the values of the APF index, or of the APF products, between successive terms.
## Results

With `j : L →ₐ[K] SeparableClosure K` an embedding:

- `apfRamificationBound_eq_of_apfSubgroup_eq_top_iff`: if for all `u ≥ -1` the APF product of `j(L)` at `u` is the whole group exactly when `u ≤ b`, then the ramification bound is `b`.
- `apfIndex_eq_one_of_apfSubgroup_eq_top`, `apfPsi_eq_self_of_apfSubgroup_eq_top`: where the product is the whole group the index is `1`, and `apfPsi K L b = b` at such `b ≥ 0`.
- `apfRamificationBound_eq_apfPsi_of_apfSubgroup_eq_top_iff`: under the hypothesis of the first item with `b ≥ 0` and `L/K` APF, the bound equals `apfPsi K L b`. This is the identity `i(L/K) = i₁` of Wintenberger §1.4.1.
- `apfStrictnessConstant_le_of_eventually_apfIndex_eq`: if the bound is at most `b` and the index equals `d` just to the right of `b`, the constant is at most `apfPsi K L b / d`.
- `apfStrictnessConstant_eq_iInf_of_index_plateaux`: let `b` be strictly increasing, tending to infinity, with `b 0 ≥ 0` equal to the ramification bound, index `1` at `b 0`, and index `d n > 0` on each interval `(b n, b (n+1)]`. Then the constant is the infimum over `n` of `apfPsi K L (b n) / d n`.
- `apfStrictnessConstant_eq_iInf_finrank_of_apfSubgroup_plateaux`: the same with the hypotheses stated on APF products; on `(b n, b (n+1)]` the product is the fixing subgroup of a finite field `E (n+1)`, and `d n` is the degree of `E (n+1)` over `K`.
- `isStrictlyAPF_iff_exists_pos_lt_of_index_plateaux`: under the hypotheses of the plateau theorem with `b 0 > 0`, strict APF is equivalent to the existence of `c > 0` with `c < apfPsi K L (b n) / d n` for all `n`.
## Proofs

The upper bound for the constant uses continuity of `apfPsi` and a limit from the right at each jump. The lower bound uses that the index is constant on each interval while `apfPsi` is increasing.

## Points to watch

- In the formula, the denominator is the degree of the field after the jump, while the numerator is the lower-numbered jump itself.
- All hypotheses about the jumps are assumptions of the theorems; this file does not construct the sequence `b`.
- Except for the first result and `apfIndex_eq_one_of_apfSubgroup_eq_top`, the results assume `IsAPF K L`.
## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Elementary.lean` (SHA-256 of the source file `904d24d56d4f579497a63c8a4b5878282782157b51532fda18ed15e402f6d6ca`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
