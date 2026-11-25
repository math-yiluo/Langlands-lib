# Herbrand change of parameter for subgroups

Module `FontaineWintenberger.Ramification.Herbrand.Subgroup`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let a finite group `G` act on a discrete valuation ring `R`, and let `H` be a subgroup, not assumed normal, acting by restriction. The file computes the composite `φ_H ∘ ψ_G` of the Herbrand function of `H` with the inverse Herbrand function of `G` as an integral of indices, and finds the first upper break of `H`. Notation: `I₀` is the zeroth lower ramification group of `G`, `A₀ = H ⊓ I₀`, and `G^u = upperRamificationGroup G u`.

## Results

- `card_lowerRamificationGroupReal_subgroup`: the real-indexed lower group of `H` at `t` has the cardinality of `H ⊓ G_t`. `card_lowerRamificationGroup_zero_subgroup`: the zeroth lower group of `H` has cardinality `|A₀|`. These two do not need `G` finite.
- `subgroup_upperRelIndex_mul_card`: for `u ≥ 0`, `[I₀ : A₀ ⊔ G^u] · |A₀| · |G^u| = |I₀| · |H_(ψ_G(u))|`.
- `subgroup_herbrand_slope_mul`: the same identity as a product of slopes, `(|H_(ψ_G(u))| / |H_0|) · (|I₀| / |G^u|) = [I₀ : A₀ ⊔ G^u]`.
- `subgroup_upperRelIndex_pos`, `subgroup_upperRelIndex_monotoneOn`, `intervalIntegrable_subgroup_upperRelIndex`: the index `[I₀ : A₀ ⊔ G^u]` is positive, nondecreasing in `u ≥ 0`, and integrable on `[0, u]`.

With the action of `G` faithful:

- `exists_subgroup_herbrand_comp_derivative_breaks`: outside a finite set of `u > 0`, `φ_H ∘ ψ_G` has derivative `[I₀ : A₀ ⊔ G^u]` at `u`.
- `subgroup_herbrandFunction_comp_inverse_eq_integral`: for `u ≥ 0`, `φ_H(ψ_G(u)) = ∫₀ᵘ [I₀ : A₀ ⊔ G^v] dv`.
- `subgroup_herbrandFunction_comp_inverse_of_nonpos`: for `−1 ≤ u ≤ 0`, `φ_H(ψ_G(u)) = u` (faithfulness not needed).
- `exists_first_upper_break_of_fixingSubgroup`: if `H ≠ ⊤` and `H ⊔ I₀ = ⊤`, there is `b ≥ 0` such that for all `u ≥ 0`, `H ⊔ G^u = ⊤` if and only if `u ≤ b`.

## Proofs

The derivative of the composite is the chain rule applied to the derivatives of `φ_H` and `ψ_G` from the earlier files, each valid off a finite set, combined with the index identity; the integral formula follows by the fundamental theorem of calculus with finitely many exceptions. For the break, `n` is the least natural number with `H ⊔ G_n ≠ ⊤` (it exists because the lower groups are eventually trivial, and `n > 0`), and `b = φ_G(n − 1)`.

## What to watch for

- `G^u` is always the upper group of the ambient group `G`; what appears is the join `A₀ ⊔ G^u` inside `I₀`, not an upper group of `H` or of a quotient.
- In the break statement the endpoint `b` belongs to the range where `H ⊔ G^u = ⊤`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Herbrand/Subgroup.lean` (SHA-256 of the source file `ce5b4e8fa195f93f2f5046275461334508f2417e847386de613420eae0823c8e`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
