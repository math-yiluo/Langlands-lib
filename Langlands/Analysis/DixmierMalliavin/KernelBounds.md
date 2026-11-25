# Bounds for the iterated exponential kernels

`Langlands.Analysis.DixmierMalliavin.KernelBounds`. Estimates for the iterated kernels `K_n`, the
remainder kernels `ρ_n` and the coefficients of `∏ (1 + a_j⁻¹ X)` of `KernelProduct`, for rates
`a j > 0` and radii `r j > 0`. All declarations are internal to the proof of the one-variable
Dixmier–Malliavin lemma (`Line`) and live in the namespace
`Langlands.Analysis.DixmierMalliavin.Line`.

## Remainder kernels

- `contDiff_stageRemainder`, `support_stageRemainder_subset`: `ρ_n` is smooth and supported in
  `[0, ∑_{j ≤ n} 2 r_j]`.
- `norm_iteratedDeriv_stageRemainder_succ_le`: if `‖η_{n+1}^{(q)}‖ ≤ B q` for all `q`, then
  `‖ρ_{n+1}^{(m)}‖ ≤ ∑_{p ≤ n+1} productCoeff a (n+1) p · B (p + m)`. Derivatives of a convolution
  with a smooth compactly supported function fall on that function
  (`iteratedDeriv_convolution`), and `K_n` has `L¹` norm at most `1` (`norm_convolution_le`).

## Fourier transforms

- `fourier_kernelProductComplex_succ`: `𝓕 K_{n+1} = 𝓕 K_n · 𝓕 k_{a_{n+1}, r_{n+1}}`.
- `norm_fourier_kernelProductComplex_le_one`: `‖𝓕 K_n‖ ≤ 1`.
- `norm_fourier_kernelProductComplex_succ_sub_le`: successive transforms differ by at most
  `4π r_{n+1} |ξ| + e^{-a_{n+1} r_{n+1}}`; with summable radii and rates this makes `𝓕 K_n`
  converge pointwise.
- `abs_pow_mul_norm_fourier_kernelProductComplex_le`: for `m ≤ n + 1`,
  `|ξ|^m ‖𝓕 K_n(ξ)‖ ≤ ∏_{j < m} a_j / π`. Each of the first `m` factors contributes
  `|ξ| ‖𝓕 k_{a_j, r_j}(ξ)‖ ≤ a_j / π`, the others at most `1`. The bound does not depend on `n`,
  which gives the uniform decay needed for the smooth weak limit.

## Coefficients

- `productCoeff_mono`: the coefficients of `∏_{j < n} (1 + a_j⁻¹ X)` increase with `n` (they are
  nonnegative and the recursion only adds nonnegative terms).
- `productCoeff_le_of`: if `β 0 = 1`, `β ≥ 0` and `a_n⁻¹ β (p - 1) ≤ 2^{-(n+1)} β p` for
  `1 ≤ p ≤ n + 1`, then `productCoeff a n p ≤ β p` for all `n` and `p`. By induction one proves the
  sharper `productCoeff a n p ≤ β p (1 - 2^{-n})` for `p ≥ 1`; the factor `2^{-(n+1)}` is what each
  new factor may add.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §2, proof of Lemma 2.5, p. 5, where the `λ_q` are
chosen one at a time so that the coefficients of `∏_{k ≤ q} (1 + x²/λₖ²)` stay below given bounds.
The page is that of the English translation *Factorizations of infinitely differentiable functions
and smooth vectors* (typeset in LaTeX, translator not named, paginated 1–24), which does not give
the pages of the original. The paper's factors are the even polynomials `1 + x²/λₖ²`, not
`1 + a_j⁻¹ X`, and its decay comes from the bound (8), p. 4, on the derivatives of the Fourier
transform `ψ_λ` of `∏ₖ (1 + x²/λₖ²)⁻¹`, not from Fourier bounds for iterated kernels.

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean`, lines 1–242 (the
whole file), of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source file:

- Namespace and names as in `KernelProduct` (`KC` → `kernelProductComplex`, `ρ` →
  `stageRemainder`, `ηC` → `expRemainderComplex`, `khat` → `expKernelFourier`, `coef` →
  `productCoeff`, `Rs` → `supportBound`).
- The file option `linter.unusedSectionVars false` is removed; unused section hypotheses are left
  out with `omit … in`, and uses pass one argument less (in one place the implicit rate sequence is
  then given by name).
- In `norm_fourier_kernelProductComplex_le_one` the deprecated `mul_le_one₀` is replaced by
  `mul_le_mul` followed by `one_mul`.
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration are added.
- Statements and proofs are otherwise unchanged.
