# Conjugation by the exponential of a divided-power family (`RootLieConj`)

Author: Worker 239.

Let `D : ℕ → Matrix (Fin n) (Fin n) ℤ` be a divided-power family (`IsDividedPowerFamily D` from
`RootExp`, by Worker 1398), and let `divExp D g = Σ_{k ≤ n} g^k D_k` be its truncated
exponential over a commutative ring. This module expands conjugation by `divExp D g` and
deduces that, over `ℚ`, such conjugation preserves every subspace that is stable under the
commutator with `D 1`.

## Results

- `IsDividedPowerFamily.pow_one`: `(D 1)^k = k! • D k`, by induction using
  `D 1 · D k = (k+1) • D (k+1)`.
- `map_intCast_zsmul`, `dp_one_mul`, `dp_mul_one`: `D 1 · D i = D i · D 1 = (i+1) • D (i+1)`
  after mapping to `R`.
- `dpSigma D m B = Σ_{a + c = m} (−1)^c D_a B D_c` (sum over the antidiagonal), the coefficient
  of `g^m`.
- `dpSigma_zero`: `σ_0(B) = B`.
- `dpSigma_succ`: `(m + 1) • σ_{m+1}(B) = D_1 σ_m(B) − σ_m(B) D_1`, from the two product rules
  above.
- `dpConj_eq_sum`: `divExp D g · B · divExp D (−g) = Σ_{m ≤ 2n} g^m σ_m(B)`. Both factors are
  expanded as a double sum over `(a, c) ∈ [0, n]²`, and the terms are regrouped by `a + c`.
- `divExp_conj_mem`: over `ℚ`, let `V` be a subspace with `[D 1, y] ∈ V` for all `y ∈ V`
  (stated with `matAd` from `RootLieAlgebra`). Then `divExp D s · x · divExp D (−s) ∈ V` for
  every `x ∈ V`. By `dpSigma_succ`, `σ_{m+1}(x) = (m+1)⁻¹ [D 1, σ_m(x)]`, so every `σ_m(x)` lies
  in `V` by induction. The conclusion then follows from `dpConj_eq_sum`.

## Provenance

The expansion follows the proof of `LieRootData.conj_eq_sum` in the module
`Langlands.GroupScheme.SplitExistence.LieRootData` (Worker 1398), here for an arbitrary
divided-power family. Mathematically, it is the identity `Ad(exp(s e)) = exp(s ad e)` for a
nilpotent matrix `e`, written with divided powers (Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §2.3; Steinberg, *Lectures on Chevalley groups*, §2).
