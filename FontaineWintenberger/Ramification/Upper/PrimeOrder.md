# Ramification for a group of prime order

Module `FontaineWintenberger.Ramification.Upper.PrimeOrder`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `G` be a group of prime order acting by ring automorphisms on a discrete valuation ring `B`. Since every subgroup of `G` is trivial or everything, the ramification filtration has a single break. The file proves this, and computes the lower groups, the upper groups and the Herbrand function from the common ramification order of the non-trivial elements.

## Main results

- `ramificationOrder_eq_of_prime_card`: if `G` has prime order, any two elements `g ≠ 1`, `h ≠ 1` have the same `ramificationOrder`.
- `exists_common_ramificationOrder_of_prime_card`: if moreover the action is faithful, this common order is a natural number `m`.
- `exists_common_ramificationOrder_succ_of_prime_card`: if moreover the zero lower ramification group is all of `G`, the common order has the form `t + 1`.

The remaining results take as hypothesis that all `g ≠ 1` have the same finite order, and need no assumption on the order of `G`:

- `lowerRamificationGroup_nat_of_common_order`: if the common order is `m`, the `n`-th lower group, for a natural number `n`, is `G` when `n < m` and trivial otherwise.
- `lowerRamificationGroupReal_of_common_order`: the lower group at a real index `s` is `G` when `s ≤ m - 1` and trivial otherwise.
- `herbrandFunction_common_break`: if `G` is finite and the common order is `t + 1`, then `herbrandFunction G t = t`.
- `upperRamificationGroup_of_common_order`: under the same hypotheses, for `u ≥ -1` the upper group at `u` is `G` when `u ≤ t` and trivial otherwise.
- `sum_ramificationOrder_of_common_order`: the sum of the orders of the elements `g ≠ 1` is `(card G - 1) * m`.

## Proofs

For the first result, `g` lies in the `n`-th lower group exactly when `n + 1 ≤ ramificationOrder g`; each lower group is trivial or everything, so two non-trivial elements lie in the same lower groups. Finiteness of the order needs the action to be faithful. The Herbrand function at `t` is computed from its expression as a sum of truncated orders. The upper groups then follow from monotonicity of the inverse Herbrand function.

## Points to watch

- `ramificationOrder` takes values in `ℕ∞`; the order of the identity is infinite for a faithful action.
- With common order `m = t + 1`, the break is at `t` in both numberings, and the groups at the break itself are still everything.
- The existence statements require a faithful action; the computations from a common order do not, and apply to any group whose non-trivial elements share one order.
- The statement on upper groups is restricted to `u ≥ -1`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/PrimeOrder.lean` (SHA-256 of the source file `bf84ce9a47ee9c245fb6d2cea92f6f1fcca9710963aa3e2a6c28d0b3125a7aa8`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
