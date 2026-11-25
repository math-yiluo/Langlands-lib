# Finite digit expansions with p-power digits over a perfect residue field

Module `FontaineWintenberger.Ramification.Lower.ResidueDigits`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `R` be a discrete valuation ring whose residue field is perfect of characteristic `p`, and `π` a uniformizer (`Irreducible π`). Every element of `R` has, to any finite precision, an expansion in powers of `π` whose digits are `p^n`-th powers.

- `exists_pow_digit_uniformizer`: for all `a`, `n` there are `b`, `c` with `a = b ^ (p ^ n) + π * c`.
- `exists_pow_digits_uniformizer`: for all `a`, `n`, `r` there are `b : ℕ → R` and `c` such that `a` is the sum over `j < r` of `b j ^ (p ^ n) * π ^ j`, plus `π ^ r * c`.
- `exists_pow_digits_sub_mem_maximalIdeal_pow`: that sum differs from `a` by an element of the `r`-th power of the maximal ideal.

The first statement lifts a `p^n`-th root of the residue class of `a`; the second is an induction on `r`.

The digits are arbitrary lifts, not multiplicative representatives. Neither completeness nor a finite residue field is assumed.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/ResidueDigits.lean` (SHA-256 of the source file `bfe6c89b7de4d053275ebe057b13d49e677f0d8871826c9772bc2e9d1c652b52`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
