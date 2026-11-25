# Approximate roots in the norm fields of finite extensions

Module `FontaineWintenberger.FieldOfNorms.Relative.ApproximateRoots`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field of characteristic `p`, `L/K` an infinite separable APF extension, and `Ω` a separable closure of `K` containing `L`. Let `f` be a monic polynomial of positive degree over the valuation ring of the norm field `FieldOfNorms K L`, separable over that field. The file shows that for every precision `r` there are a finite extension `N` of `L` in `Ω` with `[N:L] ≤ deg f` and an integral element `z` of `FieldOfNorms K N` such that `f(z)` has valuation at most `exp(-r)`.

## Main definitions

* `rootFiniteLayer K L E x hx`: for `E` a finite subextension of `L/K` and `x` integral over `E` in an extension `M` of `L`, the field `E(x)` as a finite subextension of `M/K`.
* `FieldOfNorms.integerInclusion K L M`: for `M/L` finite, the restriction of `FieldOfNorms.inclusion K L M` to the valuation rings.

## Main results

* `exists_good_fullUpper_rootFiniteLayer`: let `E.HasFullUpper K L b` hold with `b > 0`, and let `x ∈ Ω` be a root of a monic separable `g` over `𝒪[E]` with `(deg g)! · v(disc g) ≤ b`. Then `M = L(x)` has a good finite layer `D` with pullback `E`, containing `x`, with `D.HasFullUpper K M b`, and `[M:L] ≤ deg g`.
* `FieldOfNorms.exists_valuation_inclusion_eq_pow_le_finrank`: for `M/L` finite, the inclusion of norm fields raises valuations to a power `e` with `0 < e ≤ [M:L]`. `RelFieldOfNorms.stageExponent_le_finrank` and `RelFieldOfNorms.stageExponent_eq_ramificationIdx` say that `RelFieldOfNorms.stageExponent` is at most the degree and is the ramification index of `FieldOfNorms.integerInclusion`.
* `exists_fieldOfNorms_approximate_root_of_good_coordinate`: at a good layer `D` with `D.HasFullUpper K M b` and `r ≤ ⌈(p-1)/p · b⌉`, a root in the integers of `D` of the coordinate polynomial of `f` lifts to an integral `z` of `FieldOfNorms K M` with `f(z)` of valuation at most `exp(-r)`.
* `exists_fieldOfNorms_approximate_root_at_precision`: the statement of the first paragraph.
* `exists_fieldOfNorms_approximate_root_normalized`, `exists_fieldOfNorms_approximate_root`, `exists_fieldOfNorms_approximate_root_sequence`: the same with the additional bound `exp(-r / deg f)` for `RelFieldOfNorms.stageValuation`; versions for a real bound and for a sequence of precisions.

## Proofs

`FieldOfNorms.exists_coordinatePolynomial_root_stage` picks a finite layer `E` so deep that the coordinate polynomial of `f` at `E` is separable with discriminant of bounded valuation, and `E` has full upper product at a large `b`. A root `x` in `Ω` is adjoined; the results of `FontaineWintenberger.FieldOfNorms.Layers.RootDescent` give linear disjointness and the full upper product for `L(x)`. Then `FieldOfNorms.highBreakProjection_surjective` lifts `x` modulo the `r`-th power of the maximal ideal to a norm-compatible integral element.

## Remarks

Only approximate roots are produced; exact roots are not obtained here.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/ApproximateRoots.lean` (SHA-256 of the source file `3148f5090d0c00ed416b7068c8fac36aa71bde83fc59ee64fffd4842cbaeac6b`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
