# Trace class of smooth weights from trace class of convolution products

`Langlands.Analysis.Local.CompactQuotientSmoothTraceClassReduction`.

## Statements

- `Langlands.QuotientIntegration.compactQuotientSmoothTraceClass_of_convolution`: from
  `CompactQuotientConvolutionTraceClassStatement.{uG}` follows
  `CompactQuotientSmoothTraceClassStatement.{uE, uG, uA}`.
- `Langlands.QuotientIntegration.compactQuotientProductSmoothTraceClass_of_convolution`: from
  `CompactQuotientConvolutionTraceClassStatement.{max uG uB}` follows
  `CompactQuotientProductSmoothTraceClassStatement.{uE, uG, uA, uB}`.
- In `Langlands.Analysis`, for a norm-preserving representation `π` on a complex Hilbert space:
  `integratedIsometricAction_congr` (the operator depends only on the weight),
  `integratedIsometricAction_add`, `integratedIsometricAction_zero`, and
  `exists_isTraceClass_integratedIsometricAction_finsetSum` (a finite sum of weights with trace-class
  operators is integrable with trace-class operator).

## Proof

For a smooth compactly supported `f`, `Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution`
(with `U` the whole group) gives `f = ∑ᵢ φᵢ ⋆ ψᵢ` with `φᵢ`, `ψᵢ` smooth and compactly supported,
hence in `C_c(G, ℂ)`. The existing statement gives, for each `i`, integrability of `φᵢ ⋆ ψᵢ` and trace
class of its integrated operator. The integrated operator is additive in the weight, and trace-class
operators form an additive group (`Langlands.Analysis.OperatorIdeals.isTraceClass_add`), so the
sum is trace class. The product case is the same with
`Langlands.Analysis.DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod`.
