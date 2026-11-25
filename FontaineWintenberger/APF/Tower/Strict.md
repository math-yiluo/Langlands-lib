# Strict APF and the ratios of the elementary tower

Module `FontaineWintenberger.APF.Tower.Strict`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Wintenberger's criterion for strict APF in terms of the canonical elementary tower, without assuming a positive first ramification bound.

- `isStrictlyAPF_iff_exists_pos_lt_of_unbounded_index_plateaux`: let `L/K` be a separable APF extension of a complete discretely valued field, `b : ℕ → ℝ` strictly increasing with `b 0 > 0` and `b n → ∞`, and `d : ℕ → ℕ` positive and monotone with `apfIndex K L u = d n` for `b n < u ≤ b (n+1)`. Then `L/K` is strictly APF iff some `c > 0` satisfies `c < apfPsi K L (b n) / d n` for all `n`.
- `isStrictlyAPF_iff_apfElementaryLevel_div_finrank`: for an infinite APF intermediate field `L` of the separable closure, with perfect residue field, `L/K` is strictly APF iff some `c > 0` satisfies `c < apfElementaryLevel K L n / [apfElementaryStage K L (n+1) : K]` for all `n`.

The second follows from the first with `b = apfUpperBreak K L`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Strict.lean` (SHA-256 of the source file `9b6f27761b3dfe391568fdb46bfcbf379eb9863783b76753f7a13551e9f8ec03`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
