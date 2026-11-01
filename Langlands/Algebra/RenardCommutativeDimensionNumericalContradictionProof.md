# Proof of Renard C.I: the normalized numerical contradiction

Worker 1204 implements `Langlands.Renard.commutativeDimensionNumericalContradiction`, whose exact type is the unchanged published `Langlands.Renard.CommutativeDimensionNumericalContradictionStatement`. The proof assumes only natural parameters `l ≥ 1` and `k ≥ 2` and proves all six conclusions with the original real let bindings. The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, Appendix C.I, printed p.276 / one-based PDF282, registered as `renard-2026-representations-groupes-reductifs-padiques` (SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).

## Implemented calculation

Write `ε = 1 - (l : ℝ)`, `m = (k : ℝ)`, `d = 2^ε`, `r = 2-d`, `x = m^(-d)`, `D = m^r`, and `P = m^(2-2^(ε+1))`, using real powers and real arithmetic throughout. From `l ≥ 1`, the proof obtains `ε ≤ 0` and `0 < d ≤ 1`; hence `1 ≤ r`. From `k ≥ 2`, it obtains `1 < m`, so the negative exponent gives `0 < x < 1`. Thus `0 < 1-x < 1`. The positive base also gives `D > 0`, justifying division by `D` and the final multiplication back to the original inequality.

The proof applies `Real.rpow_add` to obtain `D = m*m*x`, then uses field arithmetic to obtain `m-D/m = m*(1-x)`. It also proves `2^(ε+1) = 2*d`, whence the predecessor exponent is `2-2*d = r+(-d)` and `P = D*x`. Applying `Real.mul_rpow` to the positive factors `m` and `1-x` gives

```text
(m-D/m)^r = D * (1-x)^r.
```

The preceding identities and cancellation by nonzero `D` give exactly

```text
((m-D/m)^r + P) / D = (1-x)^r + x.
```

On the base `1-x` strictly between zero and one, `Real.rpow_le_self_of_le_one` uses `r ≥ 1` to prove `(1-x)^r ≤ 1-x`. Consequently the normalized sum is at most one. The equivalence `div_le_one` for positive `D` proves `(m-D/m)^r + P ≤ D`.

When `l = 1`, the same proof includes `ε = 0`, `d = r = 1`, `x = 1/m`, `D = m`, and `P = 1`. Here the power comparison is equality by `Real.rpow_one`, and the normalization yields `(m-1)+1 = m`. Thus the final weak inequality is equality at the boundary; the proof never requires `r > 1` or `l > 1`.

## Source correspondence and scope

This implements the source's final normalization and its power comparison, preserving the predecessor exponent `2-2^(ε+1)` and the negative exponent `-d`. The final weak inequality is the derived unconditional numerical conclusion of that calculation. The implementation uses Mathlib's real-power identities directly and imports the published statement by Lean name.

The governing 2026 pages PDF281–282 and the registered supplementary 2010-edition corrections PDF18–19 were read and visually checked during the preceding statement work. The supplement, `renard-2010-corrections-complements` (SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`), concerns older exponent and inequality corrections; the 2026 formulas govern this proof.

The source separately uses an actual maximum, a floor recurrence, induction and an assumed strict counterexample to produce `D < (m-D/m)^r + P`. The theorem here proves the incompatible weak inequality without assuming that strict inequality or any recurrence. It supplies no proof of those separate dimension-theoretic steps, head/tail or maximizing-complement estimates, joint blocks or their dimension assembly, or completion of C.I or the whole-book program. The statement authors' earlier work is imported without changing its Lean/Markdown pair; the proof code in this pair is by Worker 1204.
