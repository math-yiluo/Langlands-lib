# Splitting the theta kernel with Poisson summation

Module `Langlands.Global.RankinSelberg.EqualAnalyticIdentification`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

For `D : EqualData F r`, write `Pd(g) = P(ᵗg⁻¹)` (`Pd`; in the application
`Pd = φ̃ φ̃'`), `c(t) = ∫ resLt t` and `d(t) = ∫ resGe t`.

- `poisson`: `Θ(g) + Φ(0) = e^(-L(g)) (Θι(g) + Φ̂(0))`.
- `kernel_decomp`: pointwise,
  `P |det|^s Θ = amp₁ e^(sL) + amp₂ e^((1-s)(-L)) + Φ̂(0) resLt(s-1) - Φ(0) resLt(s)`.
  On `L ≥ 0` this is the definition. On `L < 0`, substitute
  `Θ = e^(-L)(Θι + Φ̂(0)) - Φ(0)`.
- `dual_kernel_decomp`: pointwise at `ᵗg⁻¹`,
  `Pd(ᵗg⁻¹) |det ᵗg⁻¹|^s Θ(Φ̂, ᵗg⁻¹) = amp₂ e^(s(-L)) + amp₁ e^((1-s)L) + Φ(0) resGe(1-s)
  - Φ̂(0) resGe(-s)`. On `L ≥ 0`, substitute `Θι = e^L(Θ + Φ(0)) - Φ̂(0)`.
- **`integral_kernel_eq`**: `∫ K_s = A(s) + Ã(1-s) + Φ̂(0) c(s-1) - Φ(0) c(s)`, if the two
  residual integrands are integrable.
- **`integral_dual_kernel_eq`**: `∫ K̃_s = Ã(s) + A(1-s) + Φ(0) d(1-s) - Φ̂(0) d(-s)`, after the
  substitution `x ↦ ι x` on the quotient (`integral_out_iota`).
- `thetaKernelNorm_split`, `dual_thetaKernelNorm_split`, **`lintegral_kernel_lt_top`**,
  **`lintegral_dual_kernel_lt_top`**: the majorants of both kernels have finite integral for
  `Re s` beyond an explicit bound. These are exactly the hypotheses of `equalIntegral_unfold`
  for the original and the dual data.

`Pd_rational_mul`, `continuous_Pd` and `enorm_detPower_eq` are auxiliary.

## Provenance

The decomposition follows the Poisson-summation argument of Cogdell 2004, §2.3, printed p.209.
It is applied to the integral over `GL_n(F) \ GL_n(𝔸)` rather than to `E(g)` alone. The proof is
internal.
