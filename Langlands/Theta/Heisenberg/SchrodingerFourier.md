# The Fourier transform between the two Schrödinger models of a polarization

**GKT §1.2.5** (**Proposition 1.24**, p. 33: the composite `R_{Y,X} ∘ I_{X,Y} ∘ R_{X,Y}⁻¹` is the
Fourier transform; **Theorem 1.25** and **Remark 1.26**, p. 34), with Theorem 1.13 (p. 25) and
Appendix 1.A (Theorem 1.37, dual measures).

The module `Langlands.Theta.Heisenberg.SchrodingerFourier` constructs the second Schrödinger model
of a polarization and the Fourier transform between the two models, an isomorphism of
representations of the Heisenberg group, unitary for dual measures.

## Content

For a pairing `β : X →ₗ[F] Y →ₗ[F] F`, `X × Y` with `polarizedForm β` has the Lagrangians `X × 0`
and `0 × Y`. In the book's notation (`X_B = 0 × Y`, `Y_B = X × 0`, `⟨y_B, x_B⟩ = β(y_B, x_B)`):
`schrodingerSB` on `S(X)` is the book's model on `C_c^∞(Y)`, and the model on `S(Y)` is the book's
`C_c^∞(X)`.

- `polarizedForm_neg_flip_swap`, `swapHeisenbergEquiv β`: `((x, y), t) ↦ ((y, x), t)` is an
  isomorphism of Heisenberg groups `H(X × Y, polarizedForm β) ≃ H(Y × X, polarizedForm (−β.flip))`.
- `schrodingerSBDual hψ`: the Schrödinger model of the swapped polarization read through
  `swapHeisenbergEquiv`, on `S(Y)`; `((x₀, y₀), t)` acts by
  `f ↦ (y ↦ ψ(t − β(x₀, y) − ½ β(x₀, y₀)) f(y + y₀))` (`schrodingerSBDual_apply`), the book's (1.6)
  for the polarization `W = Y_B ⊕ X_B`.

Over a nonarchimedean local field, `β` perfect (`isPerfectBicharacter_psi_pairing`: `ψ ∘ β` is a
perfect pairing, GKT (1.12)), `ψ` continuous and non-trivial, `μ` a Haar measure on `X`:

- `schrodingerFourier β hψ hψ1 μ`: **`F_{Y,X} φ (y) = ∫ ψ(β(x, y)) φ(x) dμ(x)`**
  (`schrodingerFourier_apply`; `pairingFourier` of `Langlands.HarmonicAnalysis.Bicharacter.DualMeasure`).
- `schrodingerFourier_schrodinger`: **`F ∘ σ_X(h) = σ_Y(h) ∘ F`** (Theorem 1.25; translation of the
  variable of integration by `x₀`).
- `schrodingerFourierInv`: **`F_{X,Y} f (x) = ∫ ψ(−β(x, y)) f(y) dμ'(y)`** for the dual measure
  `μ' = pairingDualMeasure μ (ψ ∘ β)` (`schrodingerFourierInv_apply`), written as
  `x ↦ ℱ'_{μ'} f(−x)`.
- `schrodingerFourierEquiv`: `F` is an isomorphism of representations from `schrodingerSB` to
  `schrodingerSBDual`, with inverse `F_{X,Y}` (Remark 1.26: `F_{X,Y} = F_{Y,X}⁻¹`, no sign, because
  the two transforms use the opposite pairings); from the inversion formulas of
  `Langlands.HarmonicAnalysis.Bicharacter.DualMeasure`
  `pairingFourierDual_pairingDualMeasure_pairingFourier`,
  `pairingFourier_pairingFourierDual_pairingDualMeasure` and `pairingFourier_comp_neg`.
- `lintegral_enorm_schrodingerFourier_sq`: **`∫ |F φ|² dμ' = ∫ |φ|² dμ`** (Theorem 1.25,
  unitarity for dual measures).

Proposition 1.24 itself (the identification of `F` with the intertwiner `I_{X,Y}` of induced
models) is `lagrangianIntertwiner_inducedFunction` in `Langlands.Theta.Heisenberg.Intertwiner`, and
the partial transform of Theorem 1.27 is in `Langlands.Theta.Heisenberg.PartialFourier`.

## Declarations

- `polarizedForm_neg_flip_swap`, `swapHeisenbergEquiv`, `swapHeisenbergEquiv_apply`,
  `continuous_neg_flip_left`, `schrodingerSBDual`, `schrodingerSBDual_apply`.
- `isPerfectBicharacter_psi_pairing`, `schrodingerFourier`, `schrodingerFourier_apply`,
  `schrodingerFourier_schrodinger`, `schrodingerFourierInv`, `schrodingerFourierInv_apply`,
  `schrodingerFourierEquiv`, `schrodingerFourierEquiv_apply`,
  `lintegral_enorm_schrodingerFourier_sq`.

All in the name space `Langlands.HeisenbergGroup`.

## Dependencies

`Langlands.Theta.Heisenberg.SchrodingerInduced` (`continuous_pairing`),
`Langlands.Theta.Heisenberg.InvariantForm`, `Langlands.HarmonicAnalysis.Bicharacter.DualMeasure`
(`pairingFourier`, `pairingDualMeasure`, inversion and Plancherel).
