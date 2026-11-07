# The dual epsilon identity, nonvanishing and the unitary central value

Worker 1248. Internal lemmas, derived from the published definitions and from
the Library's Fourier normalization (`LocalFactors.padicFourierNormalization`) and
Fourier closure (`HarmonicAnalysis.padicFourierClosure`) theorems.

* The ramified test function `χ⁻¹ · 1_{O^×}` is invariant under the lattice of level
  `-a` (`ramifiedTest_eq_of_sub_mem`), hence locally constant with compact support.
* `fourier_ramifiedTest`: its plus Fourier integral at `y` is supported on the shell
  of order `-(n+a)`, where it equals `q^(-(n+a))` times the Gauss integral at `s = 0`
  times `χ(y)`. The proof substitutes `x ↦ yx` (`setIntegral_gaussShell_mul`) and uses
  Gauss shell vanishing; at `y = 0` the character average over the units vanishes.
* `gauss_mul_gauss_inv`: if `μ(O) ν(O) = q^(-n)` then `μ` and `ν` are dual for `ψ`
  by the Library normalization theorem; Fourier inversion for the test function,
  evaluated at `1`, gives
  `q^(-(n+a)) G(χ, ψ, μ) G(χ⁻¹, ψ⁻¹, ν) = 1`. No Fubini argument is used.
* `epsilonAt_mul_epsilonAt_inv`: for such `μ, ν`,
  `ε(χ, ψ, μ, s) ε(χ⁻¹, ψ⁻¹, ν, 1 - s) = 1` (the ramified case from the Gauss product
  and the spectral law, the unramified case by direct algebra).
* `exists_dual_measure` and `epsilonAt_ne_zero`: for every additive Haar measure `μ`
  some additive Haar measure `ν` (a positive multiple of `μ`) satisfies
  `μ(O) ν(O) = q^(-n)`, so the dual identity shows that `ε` never vanishes.
* `conj_gaussIntegrand`, `conj_epsilonAt`: for unitary `χ`, complex conjugation sends
  the expression for `(χ, ψ, s)` to the expression for `(χ⁻¹, ψ⁻¹, s̄)`.
* `norm_epsilonAt_half`: for unitary `χ` and `μ(O) = q^(-n/2)`, the dual identity with
  `ν = μ` at `s = 1/2` and conjugation give `|ε(1/2)|^2 = 1`.
