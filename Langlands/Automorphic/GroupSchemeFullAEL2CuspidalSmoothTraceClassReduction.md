# Cuspidal trace class of smooth test functions, from the convolution identity

`Langlands.Automorphic.GroupSchemeFullAEL2CuspidalSmoothTraceClassReduction` proves

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeFullAEL2CuspidalSmoothTraceClass_of_convolution :
  IntegratedActionConvolutionStatement.{u, u} → GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement.{u}`.

## Proof

Let `f` be a test function. By `Langlands.Global.AdelicGroupPoints.IsAdelicTestFunction.exists_eq_sum_convolution`
(`Langlands/Global/AdelicDixmierMalliavin`), `f = ∑ᵢ φᵢ ⋆ ψᵢ` for the Haar measure, with `φᵢ`, `ψᵢ`
compactly supported continuous test functions. Compactly supported continuous functions are
integrable for Haar measure. `IntegratedActionConvolutionStatement`, applied to the cuspidal
representation, gives integrability of `φᵢ ⋆ ψᵢ` and `R_cusp(φᵢ ⋆ ψᵢ) = R_cusp(φᵢ) ∘ R_cusp(ψᵢ)`; both
factors are Hilbert–Schmidt by hypothesis, so the product is trace class
(`Langlands.Analysis.OperatorIdeals.hilbertSchmidtProductTraceClass`). The integrated operator is
additive in the weight (`Langlands.Analysis.exists_isTraceClass_integratedIsometricAction_finsetSum`),
so `R_cusp(f)` is trace class.

`IntegratedActionConvolutionStatement` is a Library statement (its proof is in the Library's
`Langlands.Representation.Unitary.IntegratedConvolutionProof`, which is not used here).
