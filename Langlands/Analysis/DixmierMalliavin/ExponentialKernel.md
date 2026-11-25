# Exponential kernels of the one-variable Dixmier–Malliavin lemma

`Langlands.Analysis.DixmierMalliavin.ExponentialKernel`. The kernels from which the one-variable
Dixmier–Malliavin lemma (`Line`) is built, and the identity that drives its proof. All
declarations are internal to that proof and live in the namespace
`Langlands.Analysis.DixmierMalliavin.Line`.

## The kernels

For a radius `r > 0`, `cutoff r` is the smooth function `χ_r(t) = 1 - smoothTransition (t / r - 1)`:
it equals `1` on `(-∞, r]`, `0` on `[2r, ∞)`, and is nonincreasing (`antitone_cutoff`), so
`χ_r'` is nonpositive, vanishes outside `[r, 2r]` together with all its derivatives, and has
integral `-1`.

For a rate `a > 0`:

- `expKernel a r` is `k_{a,r}(t) = a e^{-at} χ_r(t)` for `t ≥ 0` and `0` for `t < 0`. It is
  nonnegative, bounded by `a`, supported in `[0, 2r]` and integrable.
- `expRemainder a r` is `η_{a,r}(t) = -e^{-at} χ_r'(t)`. It is smooth, nonnegative and supported
  in `[r, 2r]`.

## The step identity

`step_identity`: for `F : ℝ → ℂ` with derivative `F'` everywhere and `F'` continuous,

`F(0) = ∫ (F - a⁻¹ F') k_{a,r} + ∫ F η_{a,r}`.

It is the fundamental theorem of calculus on `[0, 2r]` for `φ(t) = F(t) e^{-at} χ_r(t)`: `φ(0) = F(0)`,
`φ(2r) = 0`, and `-φ' = (F - a⁻¹F') · a e^{-at} χ_r + F · (-e^{-at} χ_r')`. On `[0, 2r]` the two
integrals over `ℝ` are interval integrals (`integral_eq_intervalIntegral`).

Three uses of the identity in this file:

- `F = 1` gives `∫ k_{a,r} + ∫ η_{a,r} = 1` (`integral_expKernel_add_integral_expRemainder`);
  since `e^{-at} ≤ e^{-ar}` on the support of `η_{a,r}`, `∫ η_{a,r} ≤ e^{-ar}`, hence
  `1 - e^{-ar} ≤ ∫ k_{a,r} ≤ 1`.
- `F(t) = e^{-2πitξ}` gives `(1 + 2πiξ/a) 𝓕k_{a,r}(ξ) = 1 - ∫ F η_{a,r}`, whose right side has
  norm at most `2`; taking imaginary parts, `|ξ| ‖𝓕k_{a,r}(ξ)‖ ≤ a/π`
  (`abs_mul_norm_expKernelFourier_le`). This is the decay that each factor of the iterated
  convolution contributes.
- `‖𝓕k_{a,r}(ξ) - 1‖ ≤ 4πr|ξ| + e^{-ar}` (`norm_expKernelFourier_sub_one_le`): the character is
  within `4πr|ξ|` of `1` on `[0, 2r]` and the mass of `k_{a,r}` within `e^{-ar}` of `1`.

## Derivatives of the remainder

`norm_iteratedDeriv_expRemainder_le`: there is `S ≥ 0`, independent of `a`, with
`‖η_{a,r}^{(q)}(t)‖ ≤ 2^q (1+a)^q e^{-ar} S` (Leibniz rule; the derivatives of `χ_r'` are bounded and
vanish outside `[r, 2r]`, where `e^{-at} ≤ e^{-ar}`). As `(1+a)^q e^{-ar} → 0`, every derivative
of `η_{a,r}` becomes uniformly small for large `a` and fixed `r`
(`eventually_norm_iteratedDeriv_expRemainder_le`). This is what allows the rates to be chosen in
`Line`.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §2, Lemma 2.5, p. 5. The page is that of the
English translation *Factorizations of infinitely differentiable functions and smooth vectors*
(typeset in LaTeX, translator not named, paginated 1–24), which does not give the pages of the
original. The kernels and estimates of this file are those of the Lean source below; the paper
proves its Lemma 2.5 (pp. 5–6) not with exponential kernels but with the Fourier transform `ψ_λ` of
the even function `∏ₖ (1 + x²/λₖ²)⁻¹` (2.2–2.4, pp. 3–4).

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean`, lines 1–463 (the
whole file), of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source file:

- Namespace `GroundTheory.Automorphic.LineKernel` becomes `Langlands.Analysis.DixmierMalliavin.Line`.
- Names: `kern` → `expKernel`, `rem` → `expRemainder`, `khat` → `expKernelFourier`, in the
  definitions and in every lemma name containing them.
- `import Mathlib` is replaced by the Mathlib modules the file uses.
- A module docstring and a docstring for every declaration are added (the source has no comments).
- Statements and proofs are otherwise unchanged.
