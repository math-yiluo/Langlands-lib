# Integral norms between finite intermediate fields

Module `FontaineWintenberger.FieldOfNorms.Estimates.Integral`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `Ω/K` a separable algebraic extension. For finite intermediate fields `E ≤ F` of `Ω/K`, the field norm `F → E` restricts to the spectral integer rings. The file defines this restricted norm and proves its functoriality and the first congruence properties used for the field of norms.

## Definition

- `integerNorm E F hEF`: the multiplicative map `spectralIntegerRing K F → spectralIntegerRing K E`, defined as Mathlib's `Algebra.intNorm` for the two spectral integer rings, with `F` made an `E`-algebra through the inclusion.

## Results

- `coe_integerNorm`: the value of `integerNorm`, read in `E`, is the field norm `norm E F hEF` of the element.
- `integerNorm_self`, `integerNorm_integerNorm`: the norm of `E ≤ E` is the identity, and norms compose along `E ≤ F ≤ G`. Both are deduced from the same facts for field norms.
- `integerNorm_mem_maximalIdeal_pow`: if `x` lies in the `r`-th power of the maximal ideal of the integers of `F`, its norm lies in the `r`-th power of the maximal ideal of the integers of `E`. No normality of `F/E` is needed.
- `integerNorm_add_congruence_tower`: suppose that for `E ≤ F` and for `F ≤ G` the defect `N(x + y) − N(x) − N(y)` always lies in the `r`-th power of the maximal ideal of the target. Then the same holds for `E ≤ G`, with the same `r`.
- `integerNorm_add_congruence_of_chain`: the same along any finite chain of intermediate fields, each step of which satisfies the additive congruence modulo the `r`-th power; the chain is given as a `Relation.ReflTransGen`.

## Proofs

Each proof sets up the scalar towers and finiteness of the spectral integer rings, then applies a general statement about `Algebra.intNorm` proved earlier in the library (`intNorm_mem_maximalIdeal_pow`, `intNorm_add_congruence_tower`). The chain statement is an induction on the chain.

## To watch for

- The two additive congruence theorems do not prove any additive congruence by themselves: the congruence at each step is a hypothesis (`hE`, `hF`, `hchain`), and the conclusion keeps the same precision `r`.
- `FiniteIntermediateField` is the library's own type of finite-dimensional intermediate fields, and `spectralIntegerRing` its ring of integers for the spectral valuation.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Integral.lean` (SHA-256 of the source file `3febfbe346b36d86c9b79aa18c40e98864c6b8d7b2ee9dbf4f809391c4cd209d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
