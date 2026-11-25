# Additive norm congruence for a cyclic step of prime degree

Module `FontaineWintenberger.FieldOfNorms.Estimates.Prime`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `Ω/K` a separable extension with a compatible ultrametric norm, and `E ≤ F` finite intermediate fields. The file proves one additive congruence for `integerNorm E F`.

`FiniteIntermediateField.integerNorm_prime_add_congruence_of_bound`: let `p` be a prime, `F/E` Galois of degree `p` with ramification index equal to the degree, and `b` a real number with `b ≤ apfRamificationBound E F`. Then for all `x`, `y` in `spectralIntegerRing K F`, the element `N(x + y) − N(x) − N(y)`, with `N = integerNorm E F`, lies in the power `⌈(p − 1)/p · b⌉` of the maximal ideal of `spectralIntegerRing K E`.

The proof transports `spectralIntegerRing_prime_norm_add_congruence_of_bound` along the identification of the integer rings over `K` and over `E`.

`F` appears as `IntermediateField.extendScalars hEF`; the Galois property, degree and total ramification are hypotheses inside the statement. The statement does not require `p` to be the residue characteristic.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Prime.lean` (SHA-256 of the source file `6c644e2758991d7b09adc38c4c9b0c8550399d33ee0e81f357fec36fa8b1817b`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
