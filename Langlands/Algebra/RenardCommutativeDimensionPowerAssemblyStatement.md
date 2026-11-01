# Renard C.I: convexity and the finite-sum power comparison

Worker 709 authored the shared draft, reused here by Worker 1200,
who checked the original pages and prepared this statement contribution.
The closed Prop-valued declaration
`Langlands.Renard.CommutativeDimensionPowerAssemblyStatement`
formulates the numerical comparison in the opening reduction of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Appendix C.I, printed p.275 / one-based PDF281.
The source compares the power of the total dimension with the sum
of the powers of its simultaneous generalized eigenspace dimensions.
This pair contains no proof implementation.

The governing registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Workers 709 and 1200 read PDF281–282 and visually checked PDF281, including
the exponent comparison, convexity assertion and displayed finite
sum following the successive characteristic-space refinements.
The registered supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19 by both workers. Its old printed p.317 correction changes
the exponent comparison to a weak inequality. The 2026 edition
already uses the weak inequality and governs this statement.

## Exact power and conclusions

For every natural positive generator count `l`, define locally

```text
r : ℝ = 2 - Real.rpow 2 (1 - (l : ℝ)).
```

The subtraction `1 - l` takes place in the reals after the cast.
Both powers in the proposition are real powers, with the exact
source exponent. No natural exponent or truncated subtraction
is substituted.

The three conclusions are:

1. `1 ≤ r`.
2. Convexity of `x ↦ Real.rpow x r` on the actual nonnegative
   real half-line `Set.Ici 0`, expressed by `ConvexOn ℝ`.
3. For every natural `n` and every `x : Fin n → ℝ` with
   nonnegative entries,
   `∑ i, Real.rpow (x i) r ≤ Real.rpow (∑ i, x i) r`.

For the source's actual blocks `V_i`, take
`x i = (Module.finrank ℂ (V_i) : ℝ)`. Once their dimension sum
`∑ i, Module.finrank ℂ (V_i) = Module.finrank ℂ V` is established,
casting that identity and applying clause 3 gives exactly
`∑ i, f_l(k_i) ≤ f_l(k)`, where `f_l(t) = Real.rpow t r`.
This recovers the source's displayed comparison with its sides
reversed. The proposition has no carrier or universe parameters;
it concerns only the numerical function, and assumes no block
decomposition, dimension sum, convexity or power comparison.

Allowing arbitrary nonnegative real entries is a derived
extension of the source's nonnegative integral dimensions.
The statement includes zero entries and the empty family (`n = 0`).
Because `r ≥ 1` implies `r ≠ 0`, `Real.rpow 0 r = 0`: zero entries
contribute zero and both sides of the empty-family comparison are zero. For `l = 1`, `r = 1` and the finite-sum comparison
is an equality.

The positive generator count is essential for this unrestricted
finite-sum comparison. If `l = 0`, the exponent is zero and
two entries equal to one would require `2 ≤ 1`.
The zero-generator scalar-algebra case retains its separate
published base-case assertions. This statement does not narrow
their domain or claim that this finite-sum comparison holds at
zero generators.

## Proof provenance and remaining obligations

The published theorem
`Langlands.Renard.renardExponent_eq_dimensionExponent` identifies
the source exponent with
`Langlands.CommutingDimension.dimensionExponent l = 2 - 2/2^l`.
The successor lower bound is the published
`Langlands.CommutingDimension.dimensionExponent_succ_ge_one`.
Mathlib's `convexOn_rpow` in
`Mathlib.Analysis.Convex.SpecificFunctions.Basic` supplies convexity
of real powers with exponent at least one on the nonnegative half-line. The published generic
`Langlands.CommutingDimension.sum_rpow_le` proves the finite-sum
inequality for every nonnegative real family and exponent at
least one by finite-set induction. These are possible proof
tools; the new Lean file only states the source assertions.

The actual joint generalized eigenspaces and original actions
have a separate construction unit. Their finite support,
independence, spanning, dimension sum, restriction-image
dimension comparison and assembly of the nilpotent reduction
remain separate statement and proof obligations. This numerical
statement assumes no block decomposition, nilpotent bound or
recurrence, and it asserts no algebra-dimension estimate.
