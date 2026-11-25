# Affine pieces of the Herbrand function

Module `FontaineWintenberger.Ramification.Herbrand.Affine`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a finite group `G` acting on a discrete valuation ring `R`, the file gives the explicit affine formula for `herbrandFunction G` (written `φ`) on each interval `[n, n + 1]`, a final affine ray for a faithful action, and the corresponding statements for `inverseHerbrandFunction G` (`ψ`). Here `G_n` is `lowerRamificationGroup G (maximalIdeal R) n`.

## Results

- `truncatedRamificationOrder_affine`: for `g ∈ G` and `n ≤ t ≤ n + 1`, the truncated order of `g` at `t` equals its value at `n` plus `(t − n)` if `g ∈ G_(n+1)`, and plus `0` otherwise. `G` need not be finite here.
- `herbrandFunction_affine`: for `n ∈ ℕ` and `n ≤ t ≤ n + 1`, `φ(t) = φ(n) + (t − n) · |G_(n+1)| / |G_0|`.
- `herbrandFunction_affine_of_lower_eq_bot`: if `−1 ≤ a ≤ b` and the real-indexed lower groups `lowerRamificationGroupReal` are trivial on the open interval `(a, b)`, then `φ(b) = φ(a) + (b − a)/|G_0|`.
- `inverseHerbrandFunction_affine`: for `φ(n) ≤ u ≤ φ(n + 1)`, `ψ(u) = n + (u − φ(n)) / (|G_(n+1)| / |G_0|)`.

With the action faithful (`FaithfulSMul G R`):

- `exists_herbrandFunction_affine_tail`: there is `N ∈ ℕ` with `φ(t) = φ(N) + (t − N)/|G_0|` for all `t ≥ N`.
- `exists_herbrand_affine_tails`: the same `N` also gives `ψ(u) = N + (u − φ(N)) · |G_0|` for `u ≥ φ(N)`.
- `herbrandFunction_finite_affine_partition`: there is `N` such that every `t ≥ −1` falls in one of three cases, each with its formula: `t ≤ 0` and `φ(t) = t`; `t ∈ [n, n + 1]` for some `n < N`; or `t ≥ N`.
- `inverseHerbrandFunction_finite_affine_partition`: the analogous statement for `ψ`, with the intervals `[φ(n), φ(n + 1)]`.
- `exists_herbrandFunction_finite_derivative_breaks`: there is a finite set `S` of reals such that for every `t > 0` outside `S`, `φ` has derivative `|G_t| / |G_0|` at `t`, where `G_t` is the real-indexed lower group.

## Proofs

The formula on `[n, n + 1]` sums the affine formula for truncated orders over `G`, using `herbrandFunction_eq_sum`. The statement for an interval of trivial groups integrates the derivative of `φ`. The final ray uses eventual triviality of the lower groups for a faithful action. Statements on `ψ` follow by strict monotonicity and the inverse relations.

## What to watch for

- All functions here are the library's definitions for a group acting on a discrete valuation ring; no field extension appears.
- The tail and partition results assert existence of some `N`, without a bound.
- The cases of the partition overlap at endpoints: the statement is a disjunction.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Herbrand/Affine.lean` (SHA-256 of the source file `b0d307e02740bc645344318dae71339027763d9c20497474d5c5f6da05eef523`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
