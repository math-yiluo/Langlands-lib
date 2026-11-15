# The ordinary unfolding from the Whittaker expansion

Module with the ordinary half of the conditional reduction
`UnequalUnfoldingReduction.md`. Notation `n = r + 1`, `m = t + 1`,
`t < r`.

## Kernels

`ordinaryKernel F h W Φ s x = W(diag(x, I)) Φ(x) |det x|^(s-(r-t)/2)`.
With `Φ = φ'` it is the integrand over `N_m(F) \ GL_m(𝔸)`; with
`Φ = W'` the Library's `unequalWhittakerIntegrand` is its value at
quotient representatives (`unequalWhittakerIntegrand_eq`).
`projectionKernel` is the Library's `unequalIntegrand` at points
(`unequalIntegrand_eq`). `detPower_unfolding_exponent` combines the
exponents `-(n-m-1)/2` and `s-1/2` into `s-(n-m)/2`.

## Premise E: `ProjectionWhittakerExpansion F h T`

For every standard `ψ`, vector `v` and `g ∈ GL_m(𝔸)`,

`HasSum (q ↦ |det g|^{-(n-m-1)/2} W_φ(diag(ρ(q) g, I_{n-m})))
  (P^n_m φ (diag(g, 1)))`,

the sum over the countable index `RationalCosetIndex F (t+1)` of
`N_m(F) \ GL_m(F)` with chosen representatives `ρ`, where
`φ = cuspFunction F T v`, `W_φ = cuspWhittaker F T ψ v` and `P^n_m`
is the Library's `projection`. This is the displayed Fourier expansion
of Cogdell 2004, printed p.205 (PDF p.208), source
`cogdell-2004-analytic-theory-gln`:
"P^n_m φ (h 1) = |det(h)|^{-(n-m-1)/2} Σ_{γ ∈ N_m(k)\GL_m(k)}
W((γ 0; 0 1)(h I_{n-m}))", stated there "with convergence absolute
and uniform on compact subsets". Unconditional (`HasSum`) convergence
is weaker than the absolute convergence asserted by Cogdell.

## Proof of the ordinary half

`ordinaryKernel_unipotent_mul`, `ordinaryKernel_rational_mul`,
`ordinaryKernel_whittaker_unipotent_mul`: behaviour under `N_m(𝔸)`
(the generic character of `diag(n, I)` is that of `n`).
`hasSum_projectionKernel`: by E, the defining integrand is the orbit
sum of the kernel. `setIntegral_unipotent_ordinaryKernel`: averaging
the kernel of `φ'` over `N_m(F) \ N_m(𝔸)` gives the mass times the
kernel of `W'`, by the fundamental-domain formula for `W'` and
`conj(ψ⁻¹_N) = ψ_N`.

`ordinary_unfolding`: given E and integrability of
`q ↦ ordinaryKernel F h W φ' s q.out` for the Haar/counting measure on
`N_m(F) \ GL_m(𝔸)`, the Whittaker integrand is integrable for
`whittakerQuotientMeasure` and `unequalIntegral = unequalWhittakerIntegral`.
The chain is: Step 1 (orbit sum) of `UnfoldingSteps`, Step 2
(averaging), Step 3 (Whittaker quotient).
