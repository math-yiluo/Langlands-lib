# The Herbrand function and its inverse

Module `FontaineWintenberger.Ramification.Herbrand.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a finite group `G` acting on a discrete valuation ring `R` by ring automorphisms, the file defines the Herbrand function `φ` as an integral of the cardinalities of the lower ramification groups, proves that it equals a finite sum of truncated ramification orders, and shows that it is an increasing bijection of `[−1, ∞)`, which gives the inverse function `ψ`.

## Definitions

- `truncatedRamificationOrder G g t : ℝ`: the minimum of `ramificationOrder G g` and `max (t + 1) 0`, as a real number.
- `herbrandFunction G t`: equal to `t` for `t ≤ 0`, and to `∫₀ᵗ |G_s| / |G_0| ds` otherwise, where `G_s` is `lowerRamificationGroupReal G (maximalIdeal R) s`.
- `herbrandSum G t`: `(Σ(g ∈ G) truncatedRamificationOrder G g t) / |G_0| − 1`.
- `herbrandOrderIso G`: the order isomorphism of `Set.Ici (−1)` induced by `herbrandFunction`.
- `inverseHerbrandFunction G u`: the inverse isomorphism applied to `max u (−1)`.

## Results

- Truncated orders are nonnegative, continuous and monotone in `t`. `hasDerivAt_truncatedRamificationOrder`: for `t > −1` with `t + 1` not a natural number, the derivative at `t` is `1` if `g ∈ G_t` and `0` otherwise.
- `hasDerivAt_herbrandSum`: under the same condition, `herbrandSum` has derivative `|G_t| / |G_0|`.
- `integral_card_lower_eq_herbrandSum`, `herbrandFunction_eq_sum`: `herbrandFunction G t = herbrandSum G t` for all `t ≥ −1`.
- `continuousOn_herbrandFunction`, `hasDerivAt_herbrandFunction`, `strictMonoOn_herbrandFunction`: on `[−1, ∞)`, `φ` is continuous and strictly increasing, with derivative `|G_t| / |G_0|` away from the points `n − 1`.
- `herbrandFunction_lower_bound`: `(t + 1)/|G_0| − 1 ≤ φ(t)` for `t ≥ −1`.
- `surjOn_herbrandFunction`: `φ` maps `[−1, ∞)` onto itself.
- `herbrandFunction_inverseHerbrandFunction`, `inverseHerbrandFunction_herbrandFunction`: `φ` and `ψ` are mutually inverse on `[−1, ∞)`. Also, `ψ` is continuous, strictly increasing on `[−1, ∞)`, has values `≥ −1`, and `ψ(u) = u` for `−1 ≤ u ≤ 0`.

## Proofs

The sum and the integral agree because the sum is continuous, vanishes at `0`, and has the integrand as derivative outside a countable set. Strict monotonicity comes from the summand of the identity element, which is `t + 1`; surjectivity from the lower bound and the intermediate value theorem.

## What to watch for

- The functions are attached to a group action on a discrete valuation ring, not to a field extension. The normalization divides by `|G_0|`, so `G` may act nontrivially on the residue field.
- `herbrandFunction` is the identity for all `t ≤ 0`; its properties are stated on `[−1, ∞)`.
- `inverseHerbrandFunction` returns `−1` for `u < −1`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Herbrand/Basic.lean` (SHA-256 of the source file `32707934b8fde3ef8fa651c1bb78f35885e43f608cd5549639828effea9bbffd`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
