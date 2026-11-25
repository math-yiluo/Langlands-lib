# Strictly APF extensions

Module `FontaineWintenberger.APF.Strict`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a complete discretely valued field `K` and a separable extension `L/K`, the file defines strict arithmetic profiniteness in the sense of Wintenberger 1.2.1 and gives criteria for it. Write `ψ(u) = apfPsi K L u` for the Herbrand integral and `i(u) = apfIndex K L u` for the intrinsic index `(G_K^0 : G_L^0 G_K^u)`.

## Definitions

- `apfStrictnessRatio K L u`: the ratio `ψ(u) / i(u)`, sent to `ℝ≥0∞` by `ENNReal.ofReal`.
- `apfStrictnessConstant K L`: the infimum of the ratio over all real `u` with `apfRamificationBound K L ≤ u`.
- `IsStrictlyAPF K L`: a class extending `IsAPF K L` by the condition that the lower limit of the ratio as `u → ∞` is positive. `isStrictlyAPF_iff` unfolds it.

## Results

- When `apfRamificationBound K L = ⊤`: every `apfSubgroup` at `u ≥ -1` is the whole group, `L/K` is APF, `i(u) = 1` for `u ≥ 0`, `ψ` and `apfPhi` are the identity, the strictness constant is `⊤`, and `L/K` is strictly APF (`isStrictlyAPF_of_bound_eq_top`). In particular `isStrictlyAPF_self` and `apfStrictnessConstant_self` for `K/K`.
- The ratio, the constant and strict APF are invariant under `K`-isomorphisms of `L` (`apfStrictnessRatio_algEquiv`, `apfStrictnessConstant_algEquiv`, `isStrictlyAPF_algEquiv`).
- `isStrictlyAPF_iff_constant_pos`: for `L/K` APF with `0 < apfRamificationBound K L`, strict APF is equivalent to `0 < apfStrictnessConstant K L`. The two directions for a finite bound are `isStrictlyAPF_of_constant_pos_of_bound_eq_coe` and `IsStrictlyAPF.constant_pos_of_bound_eq_coe` (the latter needs the bound positive).
- `IsAPF.window_mul_index_le_apfPsi`: for `0 ≤ s ≤ t`, `(t − s) · i(s) ≤ ψ(t)`.
- `IsAPF.apfPsi_div_index_ge_of_boundedGrowth`: if `i(u + ℓ) ≤ C · i(u)` for all `u ≥ U`, with `ℓ, C > 0`, then `ℓ / C ≤ ψ(v) / i(v)` for `v ≥ max (U + ℓ) ℓ`. Consequences: `IsAPF.eventually_le_apfStrictnessRatio_of_boundedGrowth` and `isStrictlyAPF_of_apfIndex_boundedGrowth`, which concludes strict APF from that growth bound, with no hypothesis on the residue field.

## Proofs

The positivity criterion splits on the bound. For a finite positive bound `b`, the lower limit controls a tail, and on the remaining bounded interval the ratio is at least `b / i(T)` because `i` is positive and monotone and `u ≤ ψ(u)`. The window estimate comes from monotonicity of the Herbrand slope under the integral.

## Points to watch

- The ratio lives in `ℝ≥0∞`, so negative real values are truncated to `0`.
- `apfStrictnessConstant` is defined for every separable extension, extending Wintenberger's formula; with an infinite ramification bound the infimum is over the empty set and equals `⊤`.
- The equivalence with positivity of the constant assumes a positive first ramification bound.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1, in particular 1.2.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Strict.lean` (SHA-256 of the source file `d21e5df15e4e14e48dd0abc37423885890fe86d679bb942e948d899720b50c5d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
