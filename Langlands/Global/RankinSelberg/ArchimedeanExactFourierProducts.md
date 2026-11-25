# Exact adelic test and Fourier products

This module discharges the rectangular-measure premise in the existing
restricted-tensor Fourier and local-test assembly reductions. It combines
those imported results with the unconditional
`RectangleTate.rectangleTateStatement`. No new open theorem premise is
retained.

`EqualSchwartzTensor.RestrictedTensorFourierStatement.{u}` is the statement of
`RestrictedTensorFourierReductionStatement` after removing its initial
`RectangleTateStatement` premise. For a number field with compact adelic
quotient, a unitary adelic additive character trivial on the field, finite
additive support in `S`, supplied real and complex character parameters,
canonical finite components and their self-dual measures, it identifies the
Fourier transform of the actual `restrictedTensor` pointwise with the product
of the local Fourier transforms, cut off by integrality outside `S`. The
constant is exactly one. The functions at finite places in this first
statement are arbitrary; no Schwartz hypothesis is added to this identity.

`EqualSchwartzTensor.LocalFourierTestAssemblyStatement.{u}` additionally takes
Schwartz functions at all infinite places and prescribed pairs of finite
Schwartz--Bruhat row functions at `S` satisfying `IsRowFourierPair` for the
supplied measures. It constructs a global function `Phi` in the actual
`schwartzBruhat F n`, proves `IsStandardOutside F n S Phi`, and gives both
its ordinary and Fourier products pointwise with constant one. The finite
Fourier factors are exactly the prescribed partners. All character,
conductor, local-measure and local-Fourier-pair hypotheses of the original
assembly reduction remain. Arbitrary natural row dimension `n`, including
zero, empty `S`, and the free number-field universe are preserved.

The implemented proofs are direct applications:
`restrictedTensorFourier` applies `restrictedTensorFourierReduction` to
`RectangleTate.rectangleTateStatement`, and `localFourierTestAssembly` applies
`localFourierTestAssemblyReduction` to that same proof. Their proposition
definitions spell out the conclusions and all remaining binders. The imported
Fourier reduction separates the actual additive character, applies the exact
rectangular measure comparison to the Fourier kernel and treats the integral
indicator outside `S`; the imported assembly constructs the actual restricted
tensor and substitutes the prescribed finite Fourier partners. The
rectangular-measure proof establishes scalar one from the adelic covolume-one
normalization and the supplied self-dual local measures.

This supplies the test-function and exact Fourier-product clauses used for the
equal-rank archimedean factorization, in `EqualInfiniteWhittakerReduction`. It does not construct any Whittaker vectors, individual
archimedean Whittaker factors or nonvanishing local integrals, and it does not
prove `EqualPointwiseFactorizationStatement` or the full
`ArchimedeanFactorizationStatement`. Those conclusions require the remaining
Whittaker and analytic inputs.
