# Adjacent-rank literal double integral

This module supplies the absolute convergence, column change of variables, Fubini, and partial Fourier comparison for the literal adjacent-rank double integral. It is derived infrastructure for the existing image statement. Its main definition `Langlands.RankinSelberg.AdjacentDoubleIntegral.fiberNorm` is an actual square-matrix Schwartz–Bruhat function used to prove product integrability.

Fix a prime `p`, a `PadicField F`, its canonical topology and normalized absolute value, a supplied scalar additive Haar measure `ν`, an additive unitary character `ψ`, a natural `r`, a complex representation `σ` of `GL_(r+1)(F)` on `V`, a standard Whittaker functional `ℓ`, and an actual coefficient-image vector `W`. The field and carrier universes are independent. All ranks, including `r = 0`, are allowed. There is no topology or norm on `V`; every norm below is the norm of an evaluated complex number.

Write `d(h) = |det h|` for the canonical normalized absolute value and write `W(h)` for `glModelFunction ψ r σ ℓ W h`. The definition `integrand` is exactly

\[
 I_\chi(\Phi,W;x,h)
 =\Phi([h,hx])W(h^{-1})\chi(\det h)
   d(h)^{(r+2)/2}\psi(-x_{\rm last}).
\]

The powers here use the existing complex determinant weight, with the natural rank cast to the complex numbers before division by two. `Φ` is any Schwartz–Bruhat function on all `(r+1)` by `(r+2)` matrices. The product measure in the convergence theorem is the supplied `rowMeasure ν (r+1)` in `x` and the actual `generalLinearHaar F.Carrier r` in `h`.

The auxiliary `columnHomeomorph h` is `x ↦ h x`, with inverse `y ↦ h⁻¹ y`. The theorem `rowMeasure_map_mulVec` proves

\[
 (x\mapsto hx)_*\nu^{r+1}=d(h)^{-1}\nu^{r+1}.
\]

It applies the existing p-adic scalar Haar scaling theorem and its matrix-product extension. Thus no normalization scalar is silently set to one. `integrable_comp_mulVec` transports integrability, and `integral_mulVec` proves the exact Bochner substitution with real scalar `d(h)⁻¹`.

The definition `normTest` sends a Schwartz–Bruhat function `f` to the complex-valued function `z ↦ ‖f(z)‖`. Arbitrary composition preserves local constancy; the norm map sends zero to zero, so its support is contained in that of `f`. These two facts prove the Schwartz–Bruhat property. Pull back the rectangular test through the inverse of `rectangularSplit`, apply `normTest`, and take the existing Schwartz–Bruhat partial integral. The resulting definition `fiberNorm` satisfies

\[
 \operatorname{fiberNorm}(\Phi)(A)
   =\int_y\|\Phi([A,y])\|\,d\nu^{r+1}(y),
\]

where the nonnegative real integral is cast into the complex numbers. `fiberNorm_apply` proves this formula by compatibility of the integral with the real-to-complex map. `norm_fiberNorm_apply` proves that the complex norm of this value is the same nonnegative integral.

The theorem `jacobian_detWeight` proves the exact complex identity

\[
 d(h)^{-1}d(h)^{(r+2)/2}=d(h)^{r/2}.
\]

Its proof uses positivity of the determinant absolute value, addition of complex exponents, and cancellation of the nonzero determinant value. For every fixed `h`, `integrable_column` proves integrability of `x ↦ Iχ(Φ,W;x,h)` for any continuous quasicharacter `χ`. The rectangular slice, pulled back through `columnHomeomorph h`, has compact support. Its product with the continuous character phase and the constant coefficient and determinant factors is continuous with compact support. No twist restriction or smoothness of `σ` is needed for this fixed-column assertion.

Using unitarity of `ψ`, `integral_norm_column` gives the exact identity

\[
 \int_x\|I_\chi(\Phi,W;x,h)\|\,d\nu^{r+1}(x)
 =\left\|\operatorname{fiberNorm}(\Phi)(h)
     W(h^{-1})\chi(\det h)d(h)^{r/2}\right\|.
\]

It first pulls the constant norms out of the integral, applies `integral_mulVec` to the norm of the rectangular slice, and then takes the norm of `jacobian_detWeight`.

Now suppose `σ` is of full standard Whittaker type. For an arbitrary continuous base quasicharacter `χ₀`, use exactly `AdjacentCompactMatrix.realTwistedCharacter F χ₀ u` and the previously proved bound `AdjacentCompactMatrix.realTwistThreshold F ψ σ hσ ℓ χ₀`. The theorem `integrable_realTwist` proves genuine integrability of the literal two-variable kernel on the product measure whenever `u` is strictly above that bound. The bound is fixed before `u`, `W`, and `Φ`; translating `Φ` by any ambient `g` uses that same bound. The proof applies `integrable_prod_iff'`: all column sections are integrable, and `integral_norm_column` identifies the remaining real integral with the norm of the already proved square-matrix integrable function using `fiberNorm Φ`. `continuous_integrand` supplies measurability, using the smoothness contained in the Whittaker-type hypothesis. There is no extra growth or convergence premise.

The theorem `integral_column_partialFourier` proves, for arbitrary `χ`,

\[
 \int_x I_\chi(\Phi,W;x,h)\,d\nu^{r+1}(x)
 = (\mathcal F_{\rm last}\Phi)([h,h^\iota\epsilon])
      W(h^{-1})\chi(\det h)d(h)^{r/2}.
\]

Here `h^ι` is the actual inverse transpose, `ε` is the last standard basis column, and the Fourier map is `partialFourierIntegral` with inverse-character sign. The identity follows from `y=hx`: the last coordinate of `h⁻¹ y` is the pairing of the last row of `h⁻¹` with `y`. The published kernel-matrix lemmas identify that row with the last column of `adjacentRankKernelMatrix h`. Column substitution and `jacobian_detWeight` give the displayed formula with the supplied measure, without a self-duality assumption.

For the large real twists above, `double_integral_eq_partialFourier` uses the proved product integrability to apply Bochner Fubini and then the column Fourier formula. Thus it identifies the literal order `∫x ∫h` with the `h` integral on the right-hand side above; it does not merely equate totalized expressions without justifying Fubini.

With a proof that the supplied `ν` is self-dual for `ψ`, `double_integral_eq_modelIntegrand` applies this equality to `rectangularTranslate g Φ`. The defining Fourier formula and `rectangularRho0_intertwine` identify the result with the published actual tensor-model integrand on

`partialFourierEquiv ψ ν (r+1) hself Φ ⊗ W`

at any ambient `g ∈ GL_(r+2)(F)`. Finally `double_integral_eq_modelIntegral` multiplies by exactly `χ_u(det g) |det g|^((r+1)/2)` and identifies the result with `adjacentRankModelIntegral` against actual GL Haar.

The derivation combines the imported square-matrix convergence, Schwartz–Bruhat product and slice constructions, matrix Haar scaling, the existing Fourier and kernel definitions, and Bochner Fubini. Worker 1197 supplied the literal analytic comparison and its role in the image proof; Worker 455 implemented this bridge. No new premise from external literature is introduced. This contribution does not construct the common nonzero induced Whittaker functional, prove section spanning, or establish the final equality of images.
