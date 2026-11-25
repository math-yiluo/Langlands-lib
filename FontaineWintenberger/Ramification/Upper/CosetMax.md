# The largest ramification order in a coset and the Herbrand function

Module `FontaineWintenberger.Ramification.Upper.CosetMax`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be a finite Galois extension of a complete discretely valued field, `H` a normal subgroup of the Galois group, `F` its fixed field, and `ρ` the restriction to `F`. For a non-trivial automorphism `τ` of `F`, the file shows that its ramification order is determined by the largest ramification order `i(s)` among the lifts `s` of `τ`: `i_F(τ) - 1 = φ(i(s) - 1)`, where `φ` is the Herbrand function of `H` acting on the integers of `L`.

## Main results

For a group `G` acting on a discrete valuation ring `R`, with `ramificationOrder` taking values in `ℕ∞`:

- `ramificationOrder_mul_eq_min_of_coset_max`: if `s` has the largest order in its coset `sH`, then the order of `s * h` is the minimum of the orders of `h` and of `s`, for every `h` in `H`.
- `truncatedRamificationOrder_eq_coset_order`: if moreover the order of `s` is a natural number `m`, then `truncatedRamificationOrder H h (m - 1)` is the order of `s * h` as a real number.

For `L/K` as above (`ρ` is `fixedFieldDecompositionRestriction K L H`):

- `exists_fixedField_ramificationOrder_max`: every `τ ≠ 1` has a lift `s` of finite order whose order is largest among all lifts.
- `fixedField_order_sub_one_eq_herbrand`: if the residue field of `K` is perfect, `ρ s ≠ 1`, and `s` has the largest order in `sH`, then the order of `ρ s` minus 1 equals `herbrandFunction H` at the order of `s` minus 1.
- `exists_fixedField_order_eq_herbrand`: under the same hypothesis on the residue field, for every `τ ≠ 1` there is a lift `s` of finite, largest order, for which this formula holds.

## Proofs

The first result uses the rule that the order of a product is the minimum of the orders when these differ, and at least the minimum in general. The formula for the Herbrand function combines it with Tate's coset average `fixedField_order_eq_sum_div_card_inertia` from the file on fixed fields, and with the expression of the Herbrand function as a sum of truncated orders (`herbrandFunction_eq_sum`).

## Points to watch

- Orders are elements of `ℕ∞`, converted with `toNat` in the formula; the hypotheses `τ ≠ 1`, `ρ s ≠ 1` make them finite.
- The Herbrand function here is that of the subgroup `H` acting on `spectralIntegerRing K L`, with real argument.
- The order on the fixed field is `ValuationSubring.ramificationOrder` of the valuation ring of `F`, and automorphisms of `F` appear as elements of the decomposition subgroup of that ring.
- A perfect residue field is assumed for the formula, not for the existence of a largest lift.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/CosetMax.lean` (SHA-256 of the source file `6c194e5321456cf5be20ca37518d669054a12be1f149bfc79646919b50b33afa`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
