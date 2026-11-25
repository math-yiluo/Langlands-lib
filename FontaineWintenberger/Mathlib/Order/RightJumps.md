# Right jumps of monotone functions with natural values

Module `FontaineWintenberger.Mathlib.Order.RightJumps`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file studies a function `f : ℝ → ℕ` that is monotone on the positive half-line. It defines the points after which `f` increases and shows that, when `f` is locally constant from the left and unbounded, these points form an increasing sequence tending to infinity that cuts the positive half-line into intervals on which `f` is constant.

## Definition

- `IsRightJump f b`: `f b < f v` for every `v > b`. It is declared in the root namespace, for any `f : ℝ → ℕ`.

## Main results

All are in the namespace `MonotoneOn`, with hypothesis `hf : MonotoneOn f (Set.Ioi 0)`.

- `finite_setOf_rightJump_le`: for every real `U`, the set of right jumps `u` with `0 < u ≤ U` is finite.

Assume moreover `hleft`: for every `u > 0` there is `v` with `0 < v < u` such that `f` equals `f u` on `(v, u]`.

- `exists_rightJump_between`: if `0 < u`, `0 < w` and `f u < f w`, there is a right jump `b` with `u ≤ b < w` and `f b = f u`.
- `eq_of_not_rightJump`: if `0 < u ≤ v` and no point of `[u, v)` is a right jump, then `f u = f v`.

Assume also `hunbounded`: for every `n` there is `u > 0` with `n < f u`.

- `exists_rightJump_ge`: for every `u > 0` there is a right jump `b ≥ u` with `f b = f u`.
- `exists_strictMono_rightJumps`: there is a strictly increasing sequence `b : ℕ → ℝ` of positive reals, tending to infinity, such that
  - a positive real is a right jump iff it is in the range of `b`;
  - `f u = f (b (n+1))` for `b n < u ≤ b (n+1)`;
  - `f u = f (b 0)` for `0 < u ≤ b 0`.

## Proofs

In `exists_rightJump_between`, `b` is the supremum of the `v ≥ u` with `f v = f u`; left local constancy shows `f b = f u`, and maximality makes `b` a right jump. For the enumeration, `f` is strictly increasing on the positive right jumps, and its image there is an infinite set of natural numbers, order-isomorphic to `ℕ` (`Nat.Subtype.orderIsoOfNat`).

## Points to watch

- A jump point belongs to the interval on its left: at `b n`, `f` has the value of the plateau ending there.
- The sequence `b` is given by an existence statement, not as a definition.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/Order/RightJumps.lean` (SHA-256 of the source file `ad9f04a8234fdf12e2376b015413ad140885f38e3bd6993c7e50e4c5b9dd3078`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
