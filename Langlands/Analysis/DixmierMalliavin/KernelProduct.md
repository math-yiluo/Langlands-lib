# Iterated exponential kernels and the stage identity

`Langlands.Analysis.DixmierMalliavin.KernelProduct`. The iteration of the step identity of
`ExponentialKernel`, for a sequence of rates `a j > 0` and radii `r j > 0`. All declarations are
internal to the proof of the one-variable Dixmier–Malliavin lemma (`Line`) and live in the
namespace `Langlands.Analysis.DixmierMalliavin.Line`.

## Objects

- `kernelProduct a r n` is the iterated convolution `K_n = k_{a_0,r_0} ⋆ ⋯ ⋆ k_{a_n,r_n}` of
  `n + 1` exponential kernels: nonnegative, integrable, of mass at most `1`, supported in
  `[0, supportBound r n]` with `supportBound r n = ∑_{j ≤ n} 2 r_j`. `kernelProductComplex` is the
  same with complex values; `expKernelComplex` and `expRemainderComplex` are the complex
  versions of `k_{a_j,r_j}` and `η_{a_j,r_j}`.
- `productCoeff a n p` is the coefficient of `X^p` in `∏_{j < n} (1 + a_j⁻¹ X)`, defined by the
  recursion in `n`; it is nonnegative and vanishes for `p > n`. `signedCoeff a n p = (-1)^p ·
  productCoeff a n p` is the coefficient of `D^p` in `∏_{j < n} (1 - a_j⁻¹ D)`.
- `truncatedOperator a n F = ∑_{p ≤ n} signedCoeff a n p · F^{(p)}` is
  `T_n F = ∏_{j < n} (1 - a_j⁻¹ d/dt) F`; `truncatedOperator_succ` is
  `T_{n+1} F = T_n F - a_n⁻¹ (T_n F)'`.
- `stageRemainder a r n` is the remainder kernel `ρ_n`: `ρ_0 = η_0`, and
  `ρ_{n+1} = ∑_{p ≤ n+1} productCoeff a (n+1) p · (K_n ⋆ η_{n+1})^{(p)}`.

## The stage identity

`stage_identity`: for smooth `F : ℝ → ℂ` and every `n`,

`F(0) = ∫ (T_{n+1} F) K_n + ∑_{j ≤ n} ∫ F ρ_j`.

For `n = 0` this is the step identity with rate `a_0`. For the induction step, the step identity
for `t ↦ (T_{n+1} F)(s + t)` with rate `a_{n+1}`, together with
`T_{n+2} F = T_{n+1} F - a_{n+1}⁻¹ (T_{n+1} F)'`, gives
`(T_{n+1} F)(s) = ∫ (T_{n+2} F)(s + t) k_{n+1}(t) dt + ∫ (T_{n+1} F)(s + t) η_{n+1}(t) dt`.
Integrating against `K_n(s)` (`pairing_convolution`, Fubini for compactly supported kernels) turns
`∫ (T_{n+1} F) K_n` into `∫ (T_{n+2} F) K_{n+1} + ∫ (T_{n+1} F) (K_n ⋆ η_{n+1})`, and repeated
integration by parts (`integral_iteratedDeriv_mul`, `integral_truncatedOperator_mul`) moves
`T_{n+1}` onto the smooth compactly supported kernel `K_n ⋆ η_{n+1}`: the signs `(-1)^p` cancel and
the last term is `∫ F ρ_{n+1}`.

The coefficients that appear in `ρ_{n+1}` are those of `∏ (1 + a_j⁻¹ X)`, all nonnegative; in
`Line` they are kept below given weights by choosing the rates large.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §2, Lemma 2.5 and its proof, pp. 5–6. The pages
are those of the English translation *Factorizations of infinitely differentiable functions and
smooth vectors* (typeset in LaTeX, translator not named, paginated 1–24), which does not give the
pages of the original. The paper's operator is `∑ₙ (-1)ⁿ αₙ δ^{(2n)}`, with `αₙ` the coefficients of
`∏ₖ (1 + x²/λₖ²)`, and its identity is the limit (3) of Lemma 2.5 in `ℰ'(ℝ)`; the stage identity with
one-sided exponential kernels and the factors `1 - a_j⁻¹ d/dt` is the Lean source's.

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean`, lines 1–352 (the whole
file), of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source file:

- Namespace `GroundTheory.Automorphic.LineKernel` becomes `Langlands.Analysis.DixmierMalliavin.Line`.
- Names: `coef` → `productCoeff`, `sc` → `signedCoeff`, `opT` → `truncatedOperator`,
  `Kc` → `kernelProduct`, `KC` → `kernelProductComplex`, `kC` → `expKernelComplex`,
  `ηC` → `expRemainderComplex`, `ρ` → `stageRemainder`, `Rs` → `supportBound`, and the names of
  the exponential kernels as in `ExponentialKernel`, in definitions and lemma names.
- The file option `linter.unusedSectionVars false` is removed; section hypotheses that a lemma does
  not use are left out with `omit … in`, and the uses of these lemmas pass one argument less.
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration are added.
- Statements and proofs are otherwise unchanged.
