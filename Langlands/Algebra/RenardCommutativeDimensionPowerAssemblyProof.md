# Proof of Renard C.I convexity and the finite-sum power comparison

Worker 1200's theorem
`Langlands.Renard.commutativeDimensionPowerAssembly` proves exactly the closed
published proposition
`Langlands.Renard.CommutativeDimensionPowerAssemblyStatement` from
`Langlands.Algebra.RenardCommutativeDimensionPowerAssemblyStatement`.
It has no carrier or universe parameters and introduces no extra hypotheses.
The statement pair and its imports are preserved.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Appendix C.I, printed p.275 / one-based
PDF281, the exponent comparison, convexity assertion and displayed finite
sum after the successive characteristic-space refinements. The governing
registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 1200 reread PDF281–282 and visually checked PDF281 for this proof.
The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread on PDF18–19. Its correction for old printed p.317 changes the
strict exponent inequality to the weak inequality. The governing 2026
passage already uses the weak inequality.

## Exact conclusions and implemented proof

For each `l : ℕ` with `1 ≤ l`, the exponent is

```text
r : ℝ = 2 - Real.rpow 2 (1 - (l : ℝ)).
```

The inner subtraction and both powers remain real operations. The theorem
proves `1 ≤ r`, convexity of `x ↦ Real.rpow x r` on `Set.Ici (0 : ℝ)`,
and, for every `n : ℕ` and every `x : Fin n → ℝ` satisfying
`∀ i, 0 ≤ x i`,

```text
(∑ i, Real.rpow (x i) r) ≤ Real.rpow (∑ i, x i) r.
```

The proof first rewrites the exponent with the published theorem
`Langlands.Renard.renardExponent_eq_dimensionExponent` from
`Langlands.Algebra.RenardCommutativeEndomorphismDimensionProof`.
This identifies it with
`Langlands.CommutingDimension.dimensionExponent l = 2 - 2 / (2 : ℝ)^l`.
A case split on `l` rules out zero using `1 ≤ l`. At `l = k + 1`, the
published theorem
`Langlands.CommutingDimension.dimensionExponent_succ_ge_one k` from
`Langlands.Algebra.CommutingDimensionNumerics` supplies the lower bound.
This rewrite proves the lower bound for the exact source exponent; it
does not change the target proposition.

Mathlib's `convexOn_rpow` from
`Mathlib.Analysis.Convex.SpecificFunctions.Basic` then supplies the actual
`ConvexOn ℝ (Set.Ici 0)` assertion from this lower bound. Finally, the
published theorem `Langlands.CommutingDimension.sum_rpow_le` from
`Langlands.Algebra.CommutingDimensionPrimary` is applied to `Finset.univ`,
the given `x`, the same exponent, and their nonnegativity and exponent
bounds. Its real-power notation is identified with `Real.rpow` by
`Real.rpow_eq_pow`.

The reused finite-sum theorem proves the comparison by induction on a
finite set: its empty case uses `Real.zero_rpow`, and its insertion case
combines the induction hypothesis with
`Real.add_rpow_le_rpow_add`. Thus the implemented comparison follows the
two-term power inequality directly, alongside the separately proved
convexity assertion. Convexity alone is not used as an unexplained
finite-sum inference.

## Source specialization and boundaries

The assertion for arbitrary nonnegative real entries is a derived extension
of Renard's comparison for integral block dimensions. For the source's
actual blocks `V_i`, substitute
`x i = (Module.finrank ℂ (V_i) : ℝ)`. These entries are nonnegative.
Once the separate dimension-sum identity
`∑ i, Module.finrank ℂ (V_i) = Module.finrank ℂ V` is established, casting
it to the reals and rewriting the right side gives the source comparison

```text
∑ i, f_l(k_i) ≤ f_l(k),
```

where `f_l(t) = Real.rpow t r`, `k_i = dim V_i` and `k = dim V`.
This is the displayed source inequality with its sides reversed.
The proof here is numerical and does not construct the blocks or prove
their dimension sum, restriction comparisons, nilpotent reduction,
algebra-dimension estimate, recurrence or other C.I assertions. Those
retain their separate tasks and owners.

Every positive generator count is retained. At `l = 1`, `r = 1`, so the
power function is the identity and the finite-sum comparison is an
equality. Since `r ≥ 1` implies `r ≠ 0`, `Real.rpow 0 r = 0`: zero entries
are permitted, and when `n = 0` both sides are zero. The imported finite-set
induction covers these cases without any nonempty-family or strictly
positive-entry assumption.

At `l = 0`, the source exponent is zero. Two entries equal to one would
make the unrestricted finite-sum assertion read `2 ≤ 1`. The target
therefore requires `1 ≤ l`; the zero-generator scalar-algebra case remains
in the separate base-case work.

## Credit

Worker 1200 wrote this proof adapter and its explanation. Worker 746
authored the imported exponent identity. Worker 307 authored the imported
`dimensionExponent` lower bound and `sum_rpow_le` proof in the
`CommutingDimension` modules. Worker 709 authored the shared statement
draft, which Worker 1200 prepared for its earlier publication. These
published results are reused by Lean name; no unpublished proof draft is
used here.
