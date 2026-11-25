# Norm congruences at finite precision in towers

Module `FontaineWintenberger.Ramification.Norm.Tower`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `R → S` be a finite, local, injective extension of discrete valuation rings with separable extension of fraction fields, and write `N` for `Algebra.intNorm`. The file studies the additivity condition at precision `r`: `N(x + y) - N(x) - N(y)` lies in the `r`-th power of the maximal ideal of `R` for all `x`, `y`.

- `intNorm_mem_maximalIdeal_pow`: `N` maps the `r`-th power of the maximal ideal of `S` into that of `R`.
- `intNorm_sub_mem_maximalIdeal_pow_of_add_congruence`: if the additivity condition holds at precision `r` and `x - y` lies in the `r`-th power of the maximal ideal of `S`, then `N(x) - N(y)` lies in that of `R`.
- `intNorm_add_congruence_tower`: for a further finite injective extension `S → T` of discrete valuation rings, if the additivity condition holds at precision `r` for `S/R` and for `T/S`, it holds for `T/R`.

The last result uses transitivity of the integral norm.

The additivity conditions are hypotheses throughout; the file proves none of them.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Norm/Tower.lean` (SHA-256 of the source file `a81f35bdbd8c4c7328d08b60777202d3798282da492f9a0b5badcf6c111e9aef`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
