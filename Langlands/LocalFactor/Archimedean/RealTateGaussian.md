# Polynomial Gaussians are Schwartz functions

Helper module for the proof of `Langlands.LocalFactor.RealArchimedeanTateStatement`
(see `RealTateProof.md`). Authored by Worker 823. The pinned Mathlib has no Schwartz
Gaussian on `ℝ`, so this module builds one. All declarations are proved; there are no
hypotheses or axioms.

## Definitions

All declarations are in the namespace `Langlands.LocalFactor.RealTate`.

- `gaussPoly P x = P(x) exp(-π x²)` for a real polynomial `P` (real-valued).
- `gaussStep P = P' - 2π X P`, the polynomial with
  `(P e^{-πx²})' = (P' - 2π X P) e^{-πx²}`.
- `gaussSchwartz P : 𝓢(ℝ, ℂ)`, the complex-valued Schwartz function `x ↦ P(x) exp(-π x²)`.

## Results and proofs

- `hasDerivAt_gaussPoly`, `deriv_gaussPoly`: the derivative of `gaussPoly P` is
  `gaussPoly (gaussStep P)` (product and chain rule).
- `iteratedDeriv_gaussPoly`: the `n`-th derivative is `gaussPoly (gaussStep^[n] P)`
  (induction on `n`).
- `contDiff_gaussPoly`: `gaussPoly P` is smooth, by
  `contDiff_of_differentiable_iteratedDeriv`, since every iterated derivative is again a
  differentiable polynomial Gaussian.
- `exists_abs_pow_mul_exp_le`: `|x|^m exp(-π x²)` is bounded; this is the Library lemma
  `Langlands.Global.Hecke.exists_pow_mul_exp_neg_le` applied at `|x|`.
- `exists_abs_pow_mul_gaussPoly_le`: `|x|^k |P(x) exp(-π x²)|` is bounded, by bounding
  `|P(x)|` by `∑ |pᵢ| |x|^i` and applying the previous bound to each monomial.
- `gaussSchwartz`: the decay condition of `SchwartzMap` for `(k, n)` is the previous
  bound for the polynomial `gaussStep^[n] P`, using that the iterated Fréchet derivative of
  a real function of one variable has the norm of its iterated derivative
  (`norm_iteratedFDeriv_eq_norm_iteratedDeriv`) and that composing with the isometric
  embedding `ℝ → ℂ` preserves these norms.
- `gaussSchwartz_apply`: `gaussSchwartz P x = P(x) exp(-π x²)` as a complex number.
- `exists_schwartz_gaussian`: for `e : Fin 2` there is a Schwartz function equal to
  `x^e exp(-π x²)`; it is `gaussSchwartz (X^e)`.

## Provenance

The functions `x^e exp(-π x²)` are the adapted Gaussians of Tate's thesis, section 2.5
(J. T. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*,
Cassels–Fröhlich 1967, Chapter XV). That they are Schwartz functions is elementary; the
proof via the derivative recursion `gaussStep` is the implementation route chosen here.
