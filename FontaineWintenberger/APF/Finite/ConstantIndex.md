# The function ψ on an interval of constant index

Module `FontaineWintenberger.APF.Finite.ConstantIndex`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a complete discretely valued field `K` and an arithmetically profinite separable extension `L/K` (`IsAPF K L`), the file has one theorem about `ψ = apfPsi K L`.

`apfPsi_sub_apfPsi_of_apfIndex_eq`: let `0 ≤ a ≤ b` and let `c` be a natural number with `apfIndex K L u = c` for all `u` in the half-open interval `(a, b]`. Then `ψ(b) - ψ(a) = (b - a) · c`.

So `ψ` is affine of slope `c` on an interval where the index is constant. The proof splits the integral defining `ψ` at `a` and replaces the integrand by the constant `c` on `(a, b]`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Finite/ConstantIndex.lean` (SHA-256 of the source file `95d9607af985877301b784afb28be9fce564fd0d29a9f2252a2a058bfc7975f0`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
