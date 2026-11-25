# Approximating base elements by norms to finite precision

Module `FontaineWintenberger.Ramification.Norm.Approximation`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `R → S` be a finite, local, injective extension of discrete valuation rings with separable extension of fraction fields. The file shows that if `S/R` is totally ramified of degree `p ^ n`, the residue field of `R` is perfect of characteristic `p`, and the norm is additive modulo the `r`-th power of the maximal ideal of `R`, then every element of `R` is a norm modulo that power.

## Main results

- `irreducible_intNorm_of_inertiaDeg_eq_one`: if the residue degree of `S/R` is 1, the norm `Algebra.intNorm R S π` of a uniformizer `π` of `S` is a uniformizer of `R`.
- `intNorm_sum_sub_sum_intNorm_mem_maximalIdeal_pow`: if `N(x + y) - N(x) - N(y)` lies in the `r`-th power of the maximal ideal of `R` for all `x`, `y` in `S`, then the same holds for finite sums: the norm of a sum minus the sum of the norms lies in that power.
- `exists_intNorm_sub_mem_maximalIdeal_pow`: assume the ramification index equals the rank of `S` over `R` (hypothesis `he`), this rank is `p ^ n` (hypothesis `hd`), and the additivity congruence above holds at precision `r` (hypothesis `hadd`). Then for every `a` in `R` there is `α` in `S` with `N(α) - a` in the `r`-th power of the maximal ideal of `R`.
- `extensionValuationSubring_exists_intNorm_sub_mem_maximalIdeal_pow`: the same statement for `K` with `IsPerfectResidueLocalField K`, a finite separable extension `L/K`, and the valuation ring of a valuation `w` on `L` extending that of `K`, with total ramification and the degree `p ^ n` expressed on the fields.

## Proof

Total ramification gives residue degree 1, so the norm `ϖ` of a uniformizer `π'` of `S` is a uniformizer of `R`. By `exists_pow_digits_sub_mem_maximalIdeal_pow` from the file on residue digits, `a` is congruent modulo the `r`-th power to a sum of terms `b_j ^ (p ^ n) * ϖ ^ j` with `j < r`. Each term is the norm of `b_j * π' ^ j`, since the norm of an element of `R` is its `p ^ n`-th power; the additivity congruence for finite sums then gives `α = ∑ b_j * π' ^ j`.

## Points to watch

- The additivity congruence `hadd` is a hypothesis, not proved here; the caller must supply it at the precision wanted.
- The result is one finite precision at a time; nothing is said about surjectivity of the norm itself.
- The residue field must be perfect of characteristic `p`, but need not be finite.
- `IsPerfectResidueLocalField` is the library's own class.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Norm/Approximation.lean` (SHA-256 of the source file `8d7efa29860d03fabcf03afb4eea330f0fa6554da3c65e83be7d86fa0a96c841`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
