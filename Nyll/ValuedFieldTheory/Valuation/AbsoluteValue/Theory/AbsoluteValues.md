# Absolute values: equivalence, weak approximation, nonarchimedean criterion

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file sets up the basic vocabulary for real absolute values `v : AbsoluteValue K ℝ` on a field `K` used by the library's local class field theory (namespace `LubinTate.Valuations`): the associated distance, triviality, equivalence of absolute values, the weak approximation theorem, the characterization of nonarchimedean absolute values by boundedness on the integers, and Ostrowski's theorem for `ℚ`. Most statements translate the library's predicates into Mathlib's.

## Definitions

- `absoluteValueDist v x y = v (x − y)`, with the metric axioms; its uniformity is Mathlib's uniformity of `v` (`absoluteValueUniformity_basis`).
- `TrivialAbsoluteValue v`: `v x = 1` for all `x ≠ 0`; its negation is Mathlib's `v.IsNontrivial`.
- `EquivalentAbsoluteValues v w`: the identity map `WithAbs v → WithAbs w` is a homeomorphism.
- `NonarchimedeanAbsoluteValue v`: `v` is bounded on the image of `ℕ`. `ArchimedeanAbsoluteValue v` is its negation, and `StrongTriangle v` is `v (x + y) ≤ max (v x) (v y)`.

## Main results

- `equivalentAbsoluteValues_iff_isEquiv`: the library's equivalence is Mathlib's `IsEquiv`; consequently it is an equivalence relation, holds exactly when `w = v^s` for some `s > 0`, and exactly when `v` and `w` have the same open unit ball.
- `absoluteValueApproximation` (weak approximation): for finitely many nontrivial, pairwise inequivalent absolute values `vᵢ`, elements `aᵢ` and `ε > 0`, some `x` has `vᵢ(x − aᵢ) < ε` for all `i`. Helper lemmas give separating elements, bump elements and the final sum estimate.
- `nonarchimedean_iff_strong_triangle`: bounded on `ℕ` if and only if the strong triangle inequality holds; with `strong_triangle_eq_max_of_ne`, `v (x + y) = max (v x) (v y)` when `v x ≠ v y`.
- `rat_equivalent_real_or_padic`: a nontrivial absolute value on `ℚ` is equivalent to the real one or to the `p`-adic one for a unique prime `p`.

## Proof

Equivalence, the power criterion, separating elements and Ostrowski for `ℚ` come from Mathlib. The bump element is `1/(1 + z^(−n))` for large `n`, and the approximant is `∑ aⱼ eⱼ` with errors weighted by the coefficients. The nonarchimedean criterion uses the binomial estimate `v((x + y)^n) ≤ (n + 1) C max(v x, v y)^n` and `n`-th roots, through the generic lemmas of the library's imported module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean` (`AbsoluteValue.isNonarchimedean_iff_bounded_nat` and its companions).

## Points to watch

- `NonarchimedeanAbsoluteValue` is defined by boundedness on the integers, not by the strong triangle inequality; the two agree only through `nonarchimedean_iff_strong_triangle`.
- `EquivalentAbsoluteValues` is defined topologically, not as Mathlib's `IsEquiv`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Theory/AbsoluteValues.lean`: the Lean file is the source byte for byte (SHA-256 `ea21c0ce0e779e5e06667388202ae2655114490bbd27e2634b11e8aabf4a3d9b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
