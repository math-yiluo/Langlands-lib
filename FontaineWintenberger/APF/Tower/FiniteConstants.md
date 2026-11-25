# Strictness constants for finitely many jumps

Module `FontaineWintenberger.APF.Tower.FiniteConstants`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a separable extension `L/K` of a complete discretely valued field, the file gives the degree formula for `apfStrictnessConstant K L` when there are finitely many jumps.

- `isStrictlyAPF_of_finite`: every finite separable extension is strictly APF.
- `apfStrictnessConstant_eq_iInf_fin_of_index_plateaux`: let `L/K` be APF, `m ≠ 0`, `b : Fin m → ℝ` strictly increasing with `b 0 ≥ 0` equal to `apfRamificationBound K L`, `apfIndex` equal to `1` at `b 0`, and equal to `d n > 0` at every `u > b n` lying below all later `b k`. Then the constant is the infimum over `n` of `apfPsi K L (b n) / d n`.
- `apfStrictnessConstant_eq_iInf_finrank_of_finite_plateaux`: the same with hypotheses on APF products of an embedded copy of `L`; on the plateau after `b n` the product is the fixing subgroup of a finite field `E n.succ`, and `d n` is its degree over `K`.

The jump data are hypotheses.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.1, finite case.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/FiniteConstants.lean` (SHA-256 of the source file `4a284689c17740000aa3471abf369c23183119b49fa996c109a5b89a8a692528`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
