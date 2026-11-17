# Fourier coefficients of `θ ↦ (P e^{iθ} + Q e^{-iθ})^{-N}`

Author: Worker 3657. Module `Langlands.Analysis.InversePowerFourier`. Helper module of the proof
that real standard modules are nonzero (`Langlands.Archimedean.realStandardNontrivial`, module
`Langlands.Representation.Archimedean.RealStandardNontrivialProof`), used in Task 7003.
It imports only Mathlib. It changes no published file.

## Main theorems

In the namespace `Langlands.Analysis.InversePowerFourier`, with
`integrand P Q N k θ = ((P e^{iθ} + Q e^{-iθ})^N)⁻¹ · e^{-ikθ}`:

```lean
theorem integral_integrand_eq_zero {P Q : ℂ} (hPQ : ‖P‖ ≠ ‖Q‖) (N : ℕ) {k : ℤ}
    (hk : |k| < N) : ∫ θ in (0 : ℝ)..2 * Real.pi, integrand P Q N k θ = 0

theorem continuous_integrand {P Q : ℂ} (hPQ : ‖P‖ ≠ ‖Q‖) (N : ℕ) (k : ℤ) :
    Continuous (integrand P Q N k)

theorem rotated_bottom_eq (a b c d θ : ℝ) :
    ((Real.sin θ * b + Real.cos θ * d : ℝ) : ℂ) - I * ((Real.sin θ * a + Real.cos θ * c : ℝ) : ℂ) =
      rotP a b c d * exp (θ * I) + rotQ a b c d * exp (-(θ * I))

theorem norm_rotP_ne_norm_rotQ {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) :
    ‖rotP a b c d‖ ≠ ‖rotQ a b c d‖
```

The first says that, when `‖P‖ ≠ ‖Q‖`, the function `θ ↦ (P e^{iθ} + Q e^{-iθ})^{-N}` has no
Fourier mode `e^{ikθ}` with `|k| < N`. The second says that the integrand is continuous under the
same hypothesis (used to split integrals of linear combinations). The other two apply it to a rotated `2 × 2` matrix: for
`M = [[a, b], [c, d]]` and `r(θ) = [[cos θ, -sin θ], [sin θ, cos θ]]`, the bottom row of `r(θ) M` is
`(c', d') = (sin θ a + cos θ c, sin θ b + cos θ d)`, and `d' - i c' = P e^{iθ} + Q e^{-iθ}` with
`P = rotP a b c d = ((d - a) - i(c + b))/2`, `Q = rotQ a b c d = ((d + a) + i(b - c))/2`. Moreover
`|P|² - |Q|² = -(ad - bc)` (`normSq_rotP_sub_normSq_rotQ`), so `‖P‖ ≠ ‖Q‖` when `M` is invertible.
Hence `θ ↦ (d' - i c')^{-N}` has no Fourier mode `|k| < N`.

## Proofs

- **`‖P‖ < ‖Q‖` and `k < N`** (`integral_integrand_eq_zero_of_lt`). With `u = e^{iθ}`,
  `(P u + Q u⁻¹)^{-N} u^{-k} = u^{N-k} (P u² + Q)^{-N}`. The kernel
  `w ↦ w^m (P w² + Q)^{-N}`, `m = N - k - 1 ≥ 0`, is complex differentiable on the closed unit disc,
  where `‖P w²‖ ≤ ‖P‖ < ‖Q‖` keeps `P w² + Q ≠ 0`. By Mathlib's Cauchy–Goursat theorem
  (`DiffContOnCl.circleIntegral_eq_zero`) its circle integral over `|w| = 1` vanishes. Unfolding
  `circleIntegral` (`deriv_circleMap`), that integral is `i` times the Fourier coefficient.
- **`‖Q‖ < ‖P‖` and `-N < k`** (`integral_integrand_eq_zero_of_gt`). The substitution `θ ↦ -θ`
  (`intervalIntegral.integral_comp_neg`) exchanges `P` and `Q` and replaces `k` by `-k`
  (`integrand_neg`); `2π`-periodicity (`integrand_periodic`) moves the interval back to
  `[0, 2π]`.
- **`rotated_bottom_eq`**: `cos θ = (e^{iθ} + e^{-iθ})/2`, `sin θ = (e^{-iθ} - e^{iθ}) i/2`
  (`Complex.two_cos`, `Complex.two_sin`) and `i² = -1`.
- **`continuous_integrand`**: if `P e^{iθ} + Q e^{-iθ} = 0` then `‖P‖ = ‖Q‖` (both exponentials
  have norm `1`), so the base never vanishes and `Continuous.inv₀` applies.
- **`normSq_rotP_sub_normSq_rotQ`**: direct computation of real and imaginary parts.

## Provenance

This replaces the raising/lowering-operator argument suggested in the Task 7003 contract for the
Fourier condition of an induction block: in `GL_2(ℝ)`, the principal-series vector
`h ↦ |det h|^α (d - i c)^{-N}` (bottom row `(c, d)`) has, after any right translation, only
`SO(2)`-weights `|k| ≥ N`. The argument is elementary complex analysis and is internal to the
project; it makes no claim about a literature source.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`: checks 5850989e (Fourier
lemma), 0572c443 (whole module) and 949e5803 (whole module with `continuous_integrand`, built with
its dependents), no errors or warnings; axioms `propext`, `Classical.choice`, `Quot.sound`.
