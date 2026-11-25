# Principal adic filtrations on the unit ball of a complete nonarchimedean field

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.PrincipalAdicCompleteness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a nonarchimedean real absolute value on a field `K` and `O = absoluteValueValuationSubring v hnonarch` its closed unit ball. For a nonzero `π ∈ O`, the file compares the `π`-adic filtration `(π)^n` of `O` with the balls of `v`, and shows that, when `v π < 1`, this filtration is separated and, if moreover `K` is complete, precomplete. These facts feed a coefficientwise Hensel construction and an estimate on coefficients of irreducible polynomials elsewhere in the library.

## Main results

- `principal_pow_mem_iff_abs_le`: for `π ≠ 0`, `x ∈ (π)^n` if and only if `v x ≤ v(π)^n`.
- `principal_smodEq_iff_abs_sub_le`: `x ≡ y` modulo `(π)^n` if and only if `v(x − y) ≤ v(π)^n`; `abs_sub_le_of_principal_smodEq` is its forward direction.
- `principalHausdorff_of_nonzero_mem_maximalIdeal`: if `π ≠ 0` lies in the maximal ideal of `O` (that is, `v π < 1`), then `O` is Hausdorff for the ideal `(π)` (Mathlib's `IsHausdorff`).
- `principalPrecomplete_of_complete`: under the same hypotheses and `IsCompleteForAbsoluteValue v`, `O` is precomplete for `(π)` (Mathlib's `IsPrecomplete`).

## Proof

The membership criterion divides `x` by `π^n` and checks the quotient lies in `O`. Separatedness uses that `v(π)^n` tends to `0`. For precompleteness, a `(π)`-adically coherent sequence is Cauchy for `v`; its limit in `K` lies in `O` by the strong triangle inequality and is congruent to the `n`-th term modulo `(π)^n`.

## Points to watch

- Nonarchimedean is the library's predicate `LubinTate.Valuations.NonarchimedeanAbsoluteValue`, and completeness is the library's `IsCompleteForAbsoluteValue`, not Mathlib's `CompleteSpace` on `WithAbs v` directly.
- `π` need not be a uniformizer: any nonzero element with `v π < 1` works, and no discreteness of the value group is assumed.
- Only separatedness and precompleteness are proved; the file does not state that `O` is `(π)`-adically complete as a single statement, nor identify `O` with an adic completion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/PrincipalAdicCompleteness.lean`: the Lean file is the source byte for byte (SHA-256 `0c68f4bf74a6fc5bc3173b50019d9457f97eb2bd1cb333aae6edee5a241a3396`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
