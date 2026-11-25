# The norm of a sum in prime degree

Module `FontaineWintenberger.Ramification.Norm.Congruence`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a Galois extension of prime degree, `N(α + β) = N(α) + N(β) + Tr(z)` for some integral `z`. The file proves this for a group of prime order acting on a commutative ring, then for the integers of a finite Galois extension `L/K` of prime degree of a complete discretely valued field.

## Main results

For a finite group `G` of prime order acting on a commutative ring `B` by ring automorphisms:

- `exists_prod_add_sub_eq_sum_smul`: for `α`, `β` in `B` there is `z` in `B` with `∏ g • (α + β) - ∏ g • α - ∏ g • β = ∑ g • z`, products and sums over `G`.
- `exists_prod_add_sub_eq_sum_smul_mem`: if `I` is an ideal of `B` stable under `G` and `α` lies in `I`, then `z` can be taken in `I`.

For `K` a complete discretely valued field, `L/K` finite Galois, and `OL = spectralIntegerRing K L`:

- `spectralIntegerRing_algebraMap_intNorm_eq_prod`, `spectralIntegerRing_algebraMap_intTrace_eq_sum`: the integral norm and trace of `x` in `OL`, mapped back to `OL`, are the product and the sum of the conjugates of `x` under `L ≃ₐ[K] L`.
- `spectralIntegerRing_exists_intNorm_add_sub_eq_intTrace`: if `[L : K]` is prime, then `N(α + β) - N(α) - N(β)` is the integral trace of some `z` in `OL`.
- `spectralIntegerRing_exists_intNorm_add_sub_eq_intTrace_mem_pow`: if moreover `α` lies in the `r`-th power of the maximal ideal of `OL`, then `z` can be taken in that power.
- `spectralIntegerRing_intNorm_sub_sub_mem_intTraceIdeal_pow`: if `α - β` lies in the `r`-th power of the maximal ideal, then `N(α) - N(β) - N(α - β)` lies in the image of that power under the trace (`intTraceIdeal`).
- `spectralIntegerRing_intNorm_add_sub_mem_intTraceIdeal`: `N(α + β) - N(α) - N(β)` lies in the trace of the whole ring `OL`.

## Proof

Expanding `∏ g • (α + β)` gives one term for each subset `s` of `G`: the product of `g • α` over `s` times the product of `g • β` over the complement. The empty and the full subset give the two norms. The other subsets are permuted freely by left translation, because `G` has prime order, and the sum over an orbit is `∑ g • (term of a representative)`. So `z` is the sum of the terms of chosen representatives; each contains a factor `g • α`, which gives the statement with an ideal.

## Points to watch

- The degree must be prime and the extension Galois.
- The element `z` depends on a choice of orbit representatives.
- No assumption is made on the residue field, on total ramification, or on the characteristic of `K`.
- `intTraceIdeal` is the library's notion.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Norm/Congruence.lean` (SHA-256 of the source file `1c08968d1cb4b8d8ebb58fce86ac6161f7c0546d08be3417ac5b4d186ddb03c6`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
