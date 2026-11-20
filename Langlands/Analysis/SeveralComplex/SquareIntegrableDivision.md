# Square-integrable quotients by real polynomials in one variable

Module `Langlands.Analysis.SeveralComplex.SquareIntegrableDivision`
(namespace `Langlands.Analysis.SeveralComplex`). Helper of
`Langlands.Analysis.SeveralComplex.RealHyperplaneDivision` (Task 5613, Lapid
2011 Proposition 6). Provenance: internal; elementary one-variable complex
analysis. It is the one-dimensional case of the fact used in Lapid's proof of
Proposition 6 (p.330) that a pole of order `k ≥ 1` along a real hyperplane
makes `|E|²` non-integrable across it.

## Declarations

- `eq_zero_of_integrableOn_sq_div`: let `a` be real with `|a| < T`, let
  `g p : ℂ → ℂ` be continuous at `a`, and `p t ≠ 0` for almost every real `t`.
  If `t ↦ ‖g t / ((t - a) · p t)‖²` is integrable on `(-T, T)`, then
  `g a = 0`.
- `exists_eq_mul_prod_of_integrableOn`: let `f` be complex differentiable on
  `ball 0 R ⊆ ℂ`, `c ≠ 0`, and let `τ i` (`i` in a finite set `s`) be real
  with `|τ i| < T ≤ R`. If `t ↦ ‖f t / (c ∏ i ∈ s, (t - τ i))‖²` is
  integrable on the real interval `(-T, T)`, then there is `φ`, complex
  differentiable on `ball 0 R`, with `f w = c ∏ i ∈ s, (w - τ i) · φ w` on
  `ball 0 R`. Repeated roots are allowed (`τ` need not be injective).

Lean's convention `x / 0 = 0` makes the integrands total; at the finitely
many roots they are `0`, which changes nothing up to null sets.

## Proofs

`eq_zero_of_integrableOn_sq_div`: if `g a ≠ 0`, continuity gives `δ ≤ 1`
with `(-T, T) ⊇ (a - δ, a + δ)`, `‖g t‖ ≥ ‖g a‖ / 2` and `‖p t‖ ≤ ‖p a‖ + 1`
there. For almost every such `t ≠ a`,
`|t - a|⁻¹ ≤ |t - a|⁻² ≤ K ‖g t / ((t - a) p t)‖²` with
`K = (‖p a‖ + 1)² / (‖g a‖ / 2)²`. So `t ↦ (t - a)⁻¹` would be integrable on
`(a - δ, a + δ)` (`Integrable.mono'`), contradicting Mathlib's
`intervalIntegrable_sub_inv_iff`.

`exists_eq_mul_prod_of_integrableOn`, by induction on `s`. For `s = ∅` take
`φ = f / c`. For `insert i s`, write the denominator as
`(t - τ i) · p t` with `p = c ∏ j ∈ s, (· - τ j)`, which vanishes only at the
finitely many `τ j`. The previous lemma gives `f (τ i) = 0`, so
`f w = (w - τ i) · dslope f (τ i) w` (`sub_smul_dslope`) with
`dslope f (τ i)` differentiable on the disc
(`Complex.differentiableOn_dslope`). The quotient
`dslope f (τ i) t / p t` equals the old integrand for `t ≠ τ i`, hence is
square integrable, and the induction hypothesis applies to it.
