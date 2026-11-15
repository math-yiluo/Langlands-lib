# The dual unfolding from the dual Whittaker expansion

Module with the dual half of the conditional reduction
`UnequalUnfoldingReduction.md`. Notation `n = r + 1`, `m = t + 1`,
`t < r`, `w' = unfoldingWeyl F h = diag(I_m, w_{n-m})`, and
`rect(g, x) = rectangularPoint F h g x` with `x` in the rectangular
matrices `M_{n-m-1, m}(𝔸)` carrying the Library's `rectangleMeasure`.

## Rectangular integrals

`rectangleMeasure_sFinite`, `continuous_reindexGL`,
`continuous_rectangularPoint` (joint continuity in `(g, x)`),
`dualRectIntegral F h W g = ∫_x W(rect(g, x)) dx`,
`measurable_dualRectIntegral`, `measurable_dualRectNormIntegral`.

## Dual Whittaker functions

`dualWhittaker F h T ψ v = translateFunction F (r+1) w'
(dualFunction F (r+1) (cuspWhittaker F T ψ v))`, i.e.
`W̃(g) = W(w ᵗ(g w')⁻¹)`; this is the function `Wdual` of the Library
statement. `dualWhittaker_pad_mul`: `W̃(diag(n, I) y) = ψ_N(n)⁻¹ W̃(y)`.
`dualRectIntegral_unipotent_mul`, `dualRectNormIntegral_unipotent_mul`:
hence `∫_x W̃(rect(n g, x)) dx = ψ_N(n)⁻¹ ∫_x W̃(rect(g, x)) dx` and the
absolute integral is `N_m(𝔸)`-invariant.
`dualCuspWhittaker_unipotent_mul`: the dual `W̃'` of the
`ψ⁻¹`-Whittaker function of `φ'` satisfies `W̃'(n g) = ψ_N(n) W̃'(g)`.
`continuous_dualCuspFunction`, `dualCuspFunction_rational_mul`: the
dual cusp form `φ̃'` is continuous and left `GL_m(F)`-invariant.
`dualCuspWhittaker_eq_setIntegral`: `W̃'(g)` is the mass normalizer
times `∫_{fd(N_m(F))} φ̃'(n g) ψ_N(n)⁻¹ dn`, by the twist invariance
of the measure (`setIntegral_comp_dualConjUnipotent`).
`genericCharacter_inv_eq_inv`, `genericCharacter_ne_zero`.

## Kernels

`dualKernel F h W Φ s g = (∫_x W(rect(g, x)) dx) Φ(g) |det g|^(s-(r-t)/2)`;
the Library's `dualWhittakerIntegrand` is its value at quotient
representatives (`dualWhittakerIntegrand_eq`). `dualProjectionKernel` is
the Library's `dualUnequalIntegrand` at points (`dualUnequalIntegral_eq`).

## Premise E': `DualProjectionWhittakerExpansion F h T`

For every standard `ψ`, vector `v` and `g ∈ GL_m(𝔸)`, with
`φ̃ = dualFunction F (r+1) (cuspFunction F T v)` and `W̃ = dualWhittaker F h T ψ v`:

1. `x ↦ W̃(rect(g, x))` is integrable for `rectangleMeasure`;
2. `HasSum (q ↦ |det g|^{-(n-m-1)/2} ∫_x W̃(rect(ρ(q) g, x)) dx)
   (P̃ φ̃ (diag(g, 1)))`, summed over `N_m(F) \ GL_m(F)`, where
   `P̃ = dualProjection` is the Library's `ι ∘ P ∘ ι`.

Provenance: derived; this premise is the author's formulation. Cogdell
2004, printed p.207 (PDF p.210), source
`cogdell-2004-analytic-theory-gln`, states only that "one can unfold
the definitions" to obtain the rectangular dual integral and that "the
extra unipotent integration is the remnant of P̃"; E' is the pointwise
expansion that this unfolding produces. It was checked by hand for
`n = 3`, `m = 1`: writing `P̃` through the unipotent integral defining
`P`, conjugating by a permutation, inserting the mirabolic Fourier
expansion of `φ̃`, and combining the sum over `x ∈ F` with the
integral over `F \ 𝔸` gives exactly
`P̃φ̃(diag(h,1)) = |h|^{-1/2} Σ_{a ∈ F^×} ∫_𝔸 W̃(rect(a h, x)) dx`.
Absolute convergence of the inner integrals for every `g` is part of
the premise.

## Proof of the dual half

`dualKernel_unipotent_mul`, `dualKernel_rational_mul`,
`dualKernel_whittaker_unipotent_mul`, `hasSum_dualProjectionKernel`
(from E'), `setIntegral_unipotent_dualKernel` (averaging),
`norm_dualCuspWhittaker_le` (`|W̃'(g)|` is at most the mass normalizer
times `∫_{fd} |φ̃'(n g)| dn`).

`dual_unfolding`: given E' and integrability over `N_m(F) \ GL_m(𝔸)`
of `q ↦ (∫_x |W̃(rect(q.out, x))| dx) |φ̃'(q.out)| |det q.out|^(Re s-(r-t)/2)`,
the conclusion of the Library's `DualWhittakerAbsolutelyConvergent`
holds for `W̃` and `W̃'` at `s`, and
`dualUnequalIntegral F h ψ φ̃ φ̃' s = dualWhittakerIntegral F h W̃ W̃' s`.
The inner integrability comes from E'(1); the integrability of the
absolute values is obtained by dominating them with the average over
`N_m(F) \ N_m(𝔸)` of the gauge function of the hypothesis; the
equality follows the same three steps as the ordinary half.
