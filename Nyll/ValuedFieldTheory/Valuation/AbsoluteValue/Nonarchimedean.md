# Nonarchimedean absolute values are those bounded on the integers

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a real-valued absolute value `v` on a field `K`, the file proves the classical criterion: `v` satisfies the strong triangle inequality exactly when the values `v(n)`, for `n ∈ ℕ`, are bounded.

## Main result

- `AbsoluteValue.isNonarchimedean_iff_bounded_nat`: `IsNonarchimedean v` (Mathlib's predicate, `v(x + y) ≤ max(v x, v y)`) holds if and only if there is `C` with `v(n) ≤ C` for all `n ∈ ℕ`.

## Steps of the proof

- `nat_bound_ge_one`: any such bound `C` is at least `1`, since `v(1) = 1`.
- `add_pow_le_of_bounded_nat`: from the binomial theorem, `v((x + y)ⁿ) ≤ (n + 1) · C · max(v x, v y)ⁿ`.
- `add_le_root_bound_of_bounded_nat`: taking `n`-th roots, `v(x + y) ≤ ((n + 1)C)^(1/n) · max(v x, v y)` for `n ≠ 0`.
- `tendsto_linear_bound_rpow_inv`: `((n + 1)C)^(1/n) → 1` as `n → ∞`, for `C > 0`.

Letting `n → ∞` gives the strong triangle inequality. The converse direction uses Mathlib's bound `v(n) ≤ 1` for nonarchimedean `v`.

## Points to watch

The statement concerns Mathlib's `IsNonarchimedean`. Other files use the library's own predicate `NonarchimedeanAbsoluteValue`, which their proofs treat as boundedness on the image of `ℕ`. This criterion connects the two notions, but the library predicate is not mentioned in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Nonarchimedean.lean`: the Lean file is the source byte for byte (SHA-256 `f14210ad4024659e0d591bf0ca12bfe61527852415667fecd400c3e50cf5bc5d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
