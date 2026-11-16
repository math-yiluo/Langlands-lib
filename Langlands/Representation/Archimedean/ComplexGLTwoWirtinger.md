# Wirtinger derivatives on `ℂ`

Module `Langlands.Representation.Archimedean.ComplexGLTwoWirtinger`, namespace
`Langlands.Archimedean.ComplexGLTwoNoncompact`. Internal helper module for the proof of
`ComplexGLTwoMomentCompletenessStatement` (see `ComplexGLTwoMomentCompletenessProof`). It
contains standard calculus facts and no statement from the literature.

## Real-linear maps of `ℂ`

* `wirt A B : ℂ →L[ℝ] ℂ` is the real-linear map `h ↦ A h + B h̄` (`wirt_apply`).
  `wirt_add`, `wirt_sub`, `smul_wirt` and `wirt_zero` give its linearity in `(A, B)`.
* `clm_eq_wirt`: every real-linear `L : ℂ → ℂ` equals
  `wirt ((L 1 - i L i) / 2) ((L 1 + i L i) / 2)`. Proof: write `h = Re h · 1 + Im h · i`
  and `h̄ = Re h - Im h · i`, expand, and use `i² = -1`.

## Wirtinger derivatives

* `dz φ z = (Dφ(z) 1 - i Dφ(z) i) / 2` and `dzb φ z = (Dφ(z) 1 + i Dφ(z) i) / 2`, where `Dφ(z)`
  is the real Fréchet derivative `fderiv ℝ φ z`. They are the Wirtinger derivatives `∂φ` and
  `∂̄φ`, and `fderiv_eq_wirt` says `Dφ(z) = wirt (dz φ z) (dzb φ z)` (an instance of
  `clm_eq_wirt`). `fderiv_apply_eq` is the pointwise form.
* `HasWirt φ A B z` means `HasFDerivAt φ (wirt A B) z`: `φ` has real derivative
  `h ↦ A h + B h̄` at `z`. Then `dz φ z = A` and `dzb φ z = B` (`HasWirt.dz_eq`,
  `HasWirt.dzb_eq`), `φ` is real differentiable at `z`, and a real-differentiable `φ` satisfies
  `HasWirt φ (dz φ z) (dzb φ z) z` (`hasWirt_of_differentiableAt`). `HasWirt.congr` and
  `HasWirt.congr_of_eventuallyEq` rewrite the derivatives or the function near `z`.

## Rules

From the corresponding `HasFDerivAt` rules:

* constants have `(0, 0)`, the identity `(1, 0)` and `conj` has `(0, 1)`;
* sums, differences and constant multiples (`HasWirt.add`, `HasWirt.sub`,
  `HasWirt.const_mul`);
* products: `(φψ)` has `(φ A' + ψ A, φ B' + ψ B)` (`HasWirt.mul`);
* powers: `φ^n` has `(n φ^(n-1) A, n φ^(n-1) B)` (`HasWirt.pow`), and the same for integer
  powers when `φ(z) ≠ 0` (`HasWirt.zpow`);
* composition with a function `g` that has complex derivative `g'` at `φ(z)`:
  `g ∘ φ` has `(g' A, g' B)` (`HasWirt.comp_holo`).

## The weight `(1 + |z|²)^σ`

* `W z = 1 + z z̄`, which equals the real number `1 + |z|²` (`W_eq`) and is nonzero
  (`W_ne_zero`); it has Wirtinger derivatives `(z̄, z)` (`hasWirt_W`).
* `pw σ z = exp(σ log(1 + |z|²))`, i.e. `(1 + |z|²)^σ`. It is nonzero, `pw (σ + τ) = pw σ · pw τ`,
  `pw 0 = 1`, `pw 1 = W`, `pw (σ - 1) = pw σ / W` and `pw (σ + 1) = pw σ · W`.
* `pw_eq_comp`: `pw σ z = exp(σ Log(1 + z z̄))` with the principal complex logarithm, since
  `1 + |z|²` is a positive real.
* `hasWirt_pw`: `∂ pw σ = σ z̄ pw (σ - 1)` and `∂̄ pw σ = σ z pw (σ - 1)`. Proof:
  `u ↦ exp(σ Log u)` is holomorphic on the slit plane, which contains `W(z)`; apply
  `HasWirt.comp_holo` to `hasWirt_W` and simplify with `pw_sub_one`.
