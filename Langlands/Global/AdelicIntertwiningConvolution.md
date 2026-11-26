# Regular-region covariance of intertwining integrals under convolution

`IsIwasawaCompact.intertwiningOperator_integral_translate` integrates the
right-translation identity for the defining intertwining operator. It uses the
Library's normalized translate at the source parameter and at
`weylParameter l cw π' lam` on the target. For `l' ≫ π' = 𝟙 M'` this is the
Weyl transport, as in the spectral transform input. The equality applies to
the pullback along `π' ≫ cw ≫ l` for any supplied `π'`.
The integral on the right is with respect to ambient adelic Haar measure.
The hypothesis is an integrable majorant on the rational intertwining quotient
uniform over the right translates of the evaluation point by the kernel's
compact support.

Twisting cancels the target height factor. On the source, twisting the average
gives the average of the twisted inducing function evaluated at right translates.
The integrand on the product of the adelic group and the rational intertwining
quotient is continuous. This follows by pulling back along the open quotient
map and using the representative-independent formula for its value. The product
of the norm of the kernel with the given majorant is integrable. Fubini swaps
the quotient and adelic integrals, and cancellation of the nonzero target
height power gives the untwisted identity.

`IsIwasawaCompact.intertwiningOperator_sum_mul` passes a finite pointwise
linear combination through the integral when each summand is integrable. It
uses the Library's finite twist comparison with the same Iwasawa compact on
both sides.

The covariance integrates the pointwise intertwining relation in J. Arthur,
*An introduction to the trace formula* (2005), p. 34 (volume PDF p. 46),
registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`,
SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.

`intertwiningConvolutionCovariance` proves
`IntertwiningConvolutionCovarianceStatement`. The published absolute
convergence theorem gives one threshold for the original inducing form. For a
fixed parameter above that threshold and a fixed adelic argument \(g\), apply
its majorant to the compact set \(g\,\operatorname{tsupp}(a)\) and the
singleton parameter set in a complex chart. This gives covariance at every
argument for every continuous compactly supported kernel \(a\), with one
threshold independent of the kernel.
