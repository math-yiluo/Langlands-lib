# The Herbrand function of a filtered finite group

Module `Nyll.ValuedFieldTheory.Ramification.Herbrand.Function`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group `G` with a decreasing filtration `G_0 ⊇ G_1 ⊇ …` by normal subgroups, the file defines the normalized Herbrand function `φ : ℝ → ℝ` and its inverse `ψ`, and proves the sum formula expressing `φ` through the depths of the elements of `G_0`. Everything is group theory; no field appears.

## Main definitions and results

- `herbrandSlope i` is `|G_(i+1)| / |G_0|`, and `herbrandValueNat n` is the sum of the slopes for `i < n`. Slopes are positive and at least `1/|G_0|`; `herbrandValueNat` is strictly increasing.
- `herbrandFunction s` is `s` for `s < 0`, and for `s ≥ 0`, with `m = ⌊s⌋`, it is `herbrandValueNat m + (s − m)·herbrandSlope m`. So `φ` is piecewise linear with slope `|G_(m+1)|/|G_0|` on `[m, m+1]`.
- Explicit values: `φ(n) = herbrandValueNat n`; on `[m, m+1]`, `φ(s) = (Σ_(i<m) |G_(i+1)| + (s − m)·|G_(m+1)|) / |G_0|` (`herbrandFunction_eq_card_sum_of_mem_Icc`); `φ(1) = |G_1|/|G_0|`, which lies in `(0, 1]`.
- `herbrandFunction_eq_of_card_lower_eq`: two filtrations whose groups have the same orders at every level have the same `φ`.
- `herbrandFunction_strictMono`, `herbrandFunction_surjective`, `continuous_herbrandFunction`.
- `inverseHerbrandFunction` (`ψ`, defined with `Function.invFun`) is a two-sided inverse of `φ`, strictly increasing, surjective and continuous; `herbrandOrderIso` packages both as an order isomorphism of `ℝ`. Both maps preserve `[−1, ∞)`.
- `truncatedLowerDepth n σ`, for `σ ∈ G_0`, counts the `i < n` with `σ ∈ G_(i+1)`. `herbrandValueNat_eq_depth_sum` and `herbrandFunction_eq_depth_sum_of_mem_Icc` state the sum formula: `φ(s)` is `(Σ_(σ∈G_0) truncatedLowerDepth m σ + (s − m)·|G_(m+1)|) / |G_0|` for `s ∈ [m, m+1]`.

## Proofs

Continuity follows from strict monotonicity and surjectivity; surjectivity locates the right unit interval with `Nat.find`. The sum formula exchanges two finite sums of indicator functions.

## Watch for

- This is a new, shifted convention. The older `herbrandStep` of the file `GaloisValuation.Ramification` starts with `|G_0|/|G_0|` and is not the slope used here.
- `φ` is the identity on all negative reals, not only on `[−1, 0]`, and the filtration has only integer levels: on `(m, m+1)` the slope uses `G_(m+1)`.
- The classical depth `i(σ)` does not occur in the Lean statements; the docstrings relate `truncatedLowerDepth n σ` to `min(i(σ) − 1, n)`.
- `G` is finite throughout; a few lemmas drop this hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`: the Lean file is the source byte for byte (SHA-256 `da3f178d4507b719f44dc26a367c2f01e1a11a32680af4fd24df0f765acbbfcf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
