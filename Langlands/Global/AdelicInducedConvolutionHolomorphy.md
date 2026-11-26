# Entire coefficients of adelic induced convolution

`Langlands.Global.InducedConvolutionEntireCoefficientsStatement` concerns the integrated induced
action `hK.inducedConvolution λ φ v` on the adelic points of an affine group over a number field.
It takes the Iwasawa compact for `p : P → G`, a finite-dimensional parameter space
`X^*(P) ⊗ ℂ`, a continuous compactly supported kernel `φ` and a continuous inducing function `v`.
If the values of the family span a finite-dimensional space, the statement gives finitely many
members of the family that span it, with coefficients holomorphic in every complex linear
coordinate system on the whole parameter space. The subfamily can be empty if the span is zero.

## Implemented proof

`IsIwasawaCompact.isHolomorphicInCoordinatesOn_inducedConvolution` proves that, at each adelic point
`g`, the evaluation of the family is entire. In any complex linear coordinate system the
exponential factors in the integrand are exponentials of complex linear functions. The integrand
is jointly continuous in the coordinates and the integration variable by continuity of the
Iwasawa height and its parameter pairing. It vanishes off the compact support of the kernel.
Restricting Haar measure to this support gives a finite measure, and the integrand has a uniform
bound on the product of the support with any compact set of parameters. The theorem
`Langlands.Analysis.SeveralComplex.differentiableOn_integral_of_bounded` now applies. Extending the
integral back to the full group preserves its value.

`inducedConvolutionEntireCoefficients` chooses a basis from the range of the convolution family.
On this finite-dimensional span, `EisensteinJet.exists_evaluationEquiv` gives a linear isomorphism
to a tuple of point evaluations. Composing its inverse with the basis coordinate maps expresses
each coefficient as a fixed linear functional of the finite tuple of entire evaluations. These
linear functionals are continuous on the finite coordinate space, so the coefficients are entire.
The basis reconstruction formula gives the claimed pointwise expansion. The basis elements are
actual values of the family, so any condition satisfied by every member holds for them.

## Provenance

The result is the analytic and linear-algebra step in the derivation of
`InducedConvolutionFiniteSpanStatement`. The pointwise operator integrates the translates
in J. Arthur, *An introduction to the trace formula*, §7, printed pp. 33–34 (PDF pp. 45–46), with
the half-modulus absorbed into `v` as in `AdelicEisensteinConvolutionIdentity`. The source is
registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
