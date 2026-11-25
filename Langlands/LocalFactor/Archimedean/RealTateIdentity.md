# Tate's identity for real zeta integrals

Helper module for the proof of `Langlands.LocalFactor.RealArchimedeanTateStatement`
(see `RealTateProof.md`). All declarations are proved; there are
no hypotheses or axioms.

## Statement of the main result

All declarations are in the namespace `Langlands.LocalFactor.RealTate`; `zeta` and
`integrand` are from `RealTateZeta`. Write `ĥ = 𝓕⁻ h` for Mathlib's inverse Fourier
transform on `𝓢(ℝ, ℂ)`, so `ĥ(y) = ∫ exp(2π i x y) h(x) dx` (`fourierInv_apply_real`).

`tate_identity`: for Schwartz functions `f, h`, a parity `e : Fin 2` and `0 < Re u < 1`,

`Z(f, e, u) Z(ĥ, e, 1 - u) = Z(f̂, e, 1 - u) Z(h, e, u)`.

## Proof

- `kern e u z = sgn(z)^e |z|^(-u)` (and `0` at `z = 0`), defined as
  `integrand (fun _ => 1) e (1 - u) z`.
- `integrand_mul_abs_mul_integrand`: for `x ≠ 0`,
  `(f(x) sgn(x)^e |x|^(u-1)) · |x| · (φ(xz) sgn(xz)^e |xz|^(-u)) = f(x) φ(xz) k(z)`;
  this is the substitution `y = x z` written pointwise (sign and absolute-value algebra).
- `integrable_slice`, `integral_slice`, `integral_norm_slice`: for fixed `x ≠ 0`, the
  function `z ↦ f(x) φ(xz) k(z)` is integrable, with integral
  `integrand f e u x · Z(φ, e, 1 - u)` and norm integral
  `‖integrand f e u x‖ · ∫ ‖integrand φ e (1 - u)‖`, by the linear change of variables
  `Measure.integral_comp_mul_left` (`|x| · |x⁻¹| = 1`).
- `zeta_mul_zeta_eq_integral`: for `0 < Re u < 1` both `Z(f, e, u)` and `Z(φ, e, 1 - u)`
  converge absolutely, so the function `(x, z) ↦ f(x) φ(xz) k(z)` is integrable on
  `ℝ × ℝ` by `integrable_prod_iff` (the slices and the integral of slice norms are
  controlled by the previous lemmas, almost every `x` being nonzero). Fubini
  (`integral_integral_swap`) gives
  `Z(f, e, u) Z(φ, e, 1 - u) = ∫ (∫ f(x) φ(xz) dx) k(z) dz`.
- `integral_mul_fourierInv_mul`: the inner integral is symmetric,
  `∫ f(x) ĥ(xz) dx = ∫ h(w) f̂(wz) dw`; both equal the absolutely convergent double integral
  of `f(x) exp(2π i w x z) h(w)` (dominated by `|f(x)| |h(w)|`, integrable by
  `Integrable.mul_prod`), and Fubini swaps the order.
- `tate_identity`: apply `zeta_mul_zeta_eq_integral` to `(f, ĥ)` and to `(h, f̂)` and use
  the symmetry of the inner integral.

## Provenance

This is the real-place case of Tate's local identity
`ζ(f, c) ζ(ĝ, ĉ) = ζ(f̂, ĉ) ζ(g, c)`: J. T. Tate, *Fourier analysis in number fields and
Hecke's zeta-functions* (Cassels–Fröhlich 1967, Chapter XV), section 2.4, Lemma 2.4.1,
whose proof is the same substitution and Fubini argument. Here Tate's additive character
is replaced by the plus-sign kernel `exp(2π i x y)` of the Library statement, i.e.
Mathlib's inverse Fourier transform.
