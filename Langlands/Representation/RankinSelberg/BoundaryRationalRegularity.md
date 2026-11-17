# Regularity of rational continuations on the line `Re(s) = 1`

Authors: Worker 3657 (proof) and Worker 828 (verification and
submission). Module
`Langlands.Representation.RankinSelberg.BoundaryRationalRegularity`, namespace
`Langlands.RankinSelberg.UnitaryGeneric`. Helper module of the Task 6387 proof
candidate. It imports the published `HolomorphicRationalContinuationProof` and
Mathlib's Bochner integral. It changes no published file.

## Why

The published `holomorphicRationalContinuation` makes a rational continuation
regular wherever the continued function is holomorphic on an open half-plane.
For unitary generic representations the JPSS integrals are only shown to
converge on the closed half-plane `Re(s) ≥ 1` (modules `UnitaryEqualRankAnalytic`,
`UnitaryZeroRowAnalytic`), so they are holomorphic on `Re(s) > 1` only. This
module adds the boundary line using boundedness.

## Declarations

- `differentiable_spectralPoint'`: `s ↦ q^(-s)` is entire for `q > 1` (a public
  copy of a private lemma of the published module).
- `rpow_le_add_of_mem_Icc`: for `d > 0` and `1 ≤ σ ≤ 2`,
  `d^(σ-κ) ≤ d^(1-κ) + d^(2-κ)` (monotonicity of `d^x` in `x`, increasing if
  `d ≥ 1`, decreasing if `d ≤ 1`).
- `norm_integral_cpow_le_of_strip`: if `c · d^(1-κ)` and `c · d^(2-κ)` are
  integrable (`d > 0`), then for `1 ≤ Re s ≤ 2`,
  `‖∫ c · d^(s-κ)‖ ≤ ∫ (‖c · d^(1-κ)‖ + ‖c · d^(2-κ)‖)`.
- `denom_ne_zero_of_bounded_continuation`:

  ```lean
  theorem denom_ne_zero_of_bounded_continuation {q : ℕ} (hq : 1 < q) (f : ℂ → ℂ)
      (R : RatFunc ℂ) (hf : DifferentiableOn ℂ f {s : ℂ | 1 < s.re})
      (hR : HasRationalContinuation q f R) (B : ℝ)
      (hB : ∀ s : ℂ, 1 < s.re → s.re < 2 → ‖f s‖ ≤ B) :
      ∀ s : ℂ, 1 ≤ s.re → R.denom.eval (spectralPoint q s) ≠ 0
  ```

## Proof of `denom_ne_zero_of_bounded_continuation`

Write `N(s)`, `D(s)` for the numerator and denominator of `R` evaluated at
`q^(-s)`; both are entire.

1. **Cross identity.** On a right half-plane `f = N/D` (the definition of
   `HasRationalContinuation`). Both `f · D` and `N` are analytic on the connected
   open set `Re(s) > 1`, so `f · D = N` there (identity theorem), as in the
   published `holomorphicRationalContinuation`.
2. **Coprimality.** `N` and `D` have no common zero, since the numerator and the
   denominator of a `RatFunc` are coprime.
3. **`Re(s) > 1`.** If `D(s) = 0` then `N(s) = f(s) D(s) = 0`, against 2.
4. **`Re(s₀) = 1`.** Suppose `D(s₀) = 0`, so `N(s₀) ≠ 0`. For `0 < ε < 1` the
   point `s₀ + ε` lies in the strip `1 < Re < 2`, so
   `‖N(s₀+ε)‖ = ‖f(s₀+ε)‖ ‖D(s₀+ε)‖ ≤ B ‖D(s₀+ε)‖`. Letting `ε → 0⁺`
   (continuity of `N` and `D`) gives `‖N(s₀)‖ ≤ B ‖D(s₀)‖ = 0`, a contradiction.

## Provenance

This is the classical fact that a rational function bounded near a point of the
closed region has no pole there, applied to `R(q^(-s))`. Getz–Hahn deduce the
regularity on `Re(s) ≥ 1` from Proposition 11.5.1 in one sentence (Theorem
11.5.2, p.305, PDF 316, registered as
`getz-hahn-2024-automorphic-representations`); this module supplies the step
from convergence on the closed half-plane to regularity on its boundary. The route is internal to the project.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`: check
d66e9ba6 and the builds of the whole candidate; no errors or warnings.
