# Renard C.I: the normalized numerical contradiction

Worker 709 authored the draft of the closed Prop-valued declaration
`Langlands.Renard.CommutativeDimensionNumericalContradictionStatement`
for the numerical calculation ending David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Appendix C.I, printed p.276 / one-based PDF282.
It states the normalization, interval and exponent comparisons, and
the resulting inequality that excludes the source's strict
counterexample. Worker 1204 checked the source correspondence and prepared
the focused statement contribution. This pair contains no proof implementation.

The governing registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 read PDF281–282 and visually checked both pages, including
the powers in the final three displays on PDF282. Worker 1204 also read
and visually checked both pages against this pair. The registered
supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. It addresses older inequality and exponent
corrections. The 2026 edition governs the strict inequality assumed
for contradiction and every exponent here.

## Parameters and exact real powers

The parameters `l` and `k` are natural numbers with `1 ≤ l` and
`2 ≤ k`, exactly the range used for the source's strict-counterexample
calculation. All subsequent quantities are fixed real expressions,
introduced by local `let` bindings within the proposition:

| Lean name | Mathematical expression |
| --- | --- |
| `ε` | `1 - (l : ℝ)` |
| `m` | `(k : ℝ)` |
| `d` | `Real.rpow 2 ε` |
| `r` | `2 - d` |
| `x` | `Real.rpow m (-d)` |
| `D` | `Real.rpow m r` |
| `P` | `Real.rpow m (2 - Real.rpow 2 (ε + 1))` |

Thus `r = 2 - 2^(1-l)`, `D = f_l(k)` and
`P = f_(l-1)(k)` in the source's notation. Since `l` is positive,
`ε + 1 = 1 - ((l - 1 : ℕ) : ℝ)`.
Every power is a real power, including the inner power of `2`.
Every subtraction and quotient in these expressions is real; the
subtraction defining `ε` is performed after casting `l`.
No truncated natural subtraction is used for `1 - l`.

The source's negative exponent is `-(2^ε)`, represented by `-d`
in the definition of `x`. It is neither `(-2)^ε` nor `2^(-ε)`.
The locals introduce no arbitrary comparison function, supplied
exponent or replacement maximum.

## The six conclusions

The proposition states:

1. `1 ≤ r`.
2. `0 < 1 - x`.
3. `1 - x < 1`.
4. `(Real.rpow (m - D / m) r + P) / D =
   Real.rpow (1 - x) r + x`.
5. `Real.rpow (1 - x) r ≤ 1 - x`.
6. `Real.rpow (m - D / m) r + P ≤ D`.

The first three are the exponent and open-interval facts invoked
in the source's last sentence. Clause 4 identifies the right side
after dividing its preceding strict inequality by `D = f_l(k)`.
The predecessor term normalizes to `x` because its exponent
difference is `2^ε - 2^(ε+1) = -2^ε`.
Clause 5 states explicitly the power comparison behind the source's
impossibility assertion. Clause 6 packages the resulting numerical
conclusion before normalization.

The hypotheses imply `m > 0`, `d > 0`, and `D > 0`, so the source
normalization divides by a positive quantity. The normalized right
side is at most `(1 - x) + x = 1`. Consequently clause 6 rules out
the strict inequality `D < (m - D / m)^r + P` produced by the
source's assumed counterexample.

When `l = 1`, the expressions are `ε = 0`, `d = r = 1`,
`x = 1/m`, `D = m` and `P = 1`. The final weak inequality
is then an equality. This boundary is included and still excludes
the strict inequality assumed for contradiction.

This declaration states the unconditional numerical inequality in
the indicated parameter range. It assumes neither the strict
counterexample inequality nor the normalization, interval, exponent
or power comparisons. Clause 6 is an explicit derived packaging
of the source calculation, rather than a separately numbered lemma.

## Proof and remaining scope

The intended source route rewrites the two unnormalized powers
using real-power product and exponent laws, divides by positive
`D`, and uses the order of real powers on a base between zero
and one. The Lean file only states the conclusions.

The published `Langlands.CommutingDimension.dimensionExponent`
uses the equivalent exponent `2 - 2 / 2^l`.
`Langlands.CommutingDimension.real_dimension_step` proves a
different direct numerical step from complement and splitting
estimates. Those results may be reused by a future proof after
checking the exact exponent correspondence; neither is assumed
as a premise of this statement.

The actual maximum's floor recurrence, its maximizing-complement
and head/tail comparisons, the induction deriving its real-power
bound, and the general reduction from commuting endomorphisms
retain their separate obligations. The final commutative
endomorphism dimension theorem already has a published proof
through the direct numerical route; that proof alone does not
state this source normalization. This numerical statement
neither assumes a recurrence nor asserts completion of C.I or
the whole-book program.
