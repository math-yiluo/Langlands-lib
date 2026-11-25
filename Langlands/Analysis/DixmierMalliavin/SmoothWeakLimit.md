# Smooth weak limits of kernels with uniform Fourier decay

`Langlands.Analysis.DixmierMalliavin.SmoothWeakLimit`. One public theorem of real analysis on `ℝ`,
used by the one-variable Dixmier–Malliavin lemma to produce its smooth function `g`.

## Statement

`Langlands.Analysis.DixmierMalliavin.exists_contDiff_weakLimit_of_fourier_decay`. Let
`K : ℕ → ℝ → ℝ` be integrable, nonnegative, of mass `∫ K N ≤ 1`, with `support (K N) ⊆ [a, b]`.
Assume that the Fourier transforms `𝓕 (K N) ξ` converge for every `ξ`, and that for every `m` there
are `C` and `N₀` with `‖𝓕 (K N) ξ‖ ≤ C (1 + |ξ|)^{-m}` for all `N ≥ N₀` and all `ξ`. Then there is a
smooth `g : ℝ → ℂ` with `tsupport g ⊆ [a, b]` and `∫ ψ · K N → ∫ ψ · g` for every continuous
`ψ : ℝ → ℂ`.

## Proof

Let `Φ` be the pointwise limit of the `𝓕 (K N)`. It inherits the decay bounds, so
`ξ ↦ |ξ|^n Φ(ξ)` is integrable for every `n`, and `g = 𝓕⁻ Φ` is smooth (`Real.contDiff_fourier`).
For smooth compactly supported `ψ`, `ψ = 𝓕 (𝓕⁻ ψ)` (Fourier inversion through Schwartz
functions), so `∫ ψ K N = ∫ 𝓕⁻ ψ · 𝓕 (K N)` and `∫ ψ g = ∫ 𝓕⁻ ψ · Φ`
(`WeakLimit.integral_fourier_mul_eq`, `WeakLimit.integral_fourierInv_mul_eq`); dominated
convergence with the bound `‖𝓕 (K N)‖ ≤ 1` gives the convergence. Testing against smooth functions
supported outside `[a, b]` shows that `g` vanishes almost everywhere, hence everywhere, outside
`[a, b]`. A continuous `ψ` is approximated within `η` on `[a, b]` by a smooth compactly supported
function (`WeakLimit.exists_smooth_near`: Weierstrass approximation of the real and imaginary
parts times a bump function), and since the `K N` and `g` live on `[a, b]` with bounded mass, the
error is uniformly small.

## Literature

The one-variable lemma is J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs
indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), §2, Lemma 2.5, p. 5. There the
smooth function is not a weak limit of kernels: it is built in the proof (pp. 5–6) from
`ω_λ = ψ_λ · ω`, where `ψ_λ` is the Fourier transform of the rapidly decreasing function
`∏ₖ (1 + x²/λₖ²)⁻¹` (2.3, p. 4) and `ω` a cut-off. The weak limit and the Fourier-analytic argument
above are those of the Lean source. The pages are those of the English translation *Factorizations
of infinitely differentiable functions and smooth vectors* (typeset in LaTeX, translator not named,
paginated 1–24), which does not give the pages of the original.

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/DixmierMalliavinLineLimit.lean`, lines 1–219 (the whole
file), of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source file:

- Namespace `GroundTheory.Automorphic` becomes `Langlands.Analysis.DixmierMalliavin` (auxiliary
  lemmas in `…DixmierMalliavin.WeakLimit`, as in the source).
- `exists_smooth_weak_limit` is renamed `exists_contDiff_weakLimit_of_fourier_decay`; its statement
  is unchanged.
- The local abbreviation `Kc` in the proof is called `KC`.
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration are added.
