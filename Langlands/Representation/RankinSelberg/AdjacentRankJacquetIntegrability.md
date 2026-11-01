# All-section convergence of the actual adjacent Jacquet integral

This internal consequence combines normalized-section surjectivity with the
pure-section Jacquet comparison and scalar linearity. It retains the exact
canonical normalized opposite induction on the original tensor carrier, all
natural ranks including zero, independent field and module universes, and the
supplied additive Haar measure. No norm or topology is imposed on the module.

`integrable_realTwist` proves convergence of the literal scalar Jacquet kernel
for every actual section and every ambient translate, beyond the same
`AdjacentCompactMatrix.realTwistThreshold` used for pure sections. The original
representation has full Whittaker type; the given functional need not be
nonzero for this result. Surjectivity supplies a compact-test/vector tensor
preimage of any section. Tensor induction uses pure-section convergence and
additivity of `integrandLinear`. Thus convergence is uniform over sections and
translates without adding an analytic assumption.

`realTwistIntegralLinear` is the resulting unconditional linear integral at
each ambient element, under that threshold. Its coefficient formula identifies
the integral at the identity of a right translate with the literal integral
at that ambient element.

`compactTestModelTensor` maps compact full-rank tests through the specified
partial Fourier transform and original vectors through the coefficient
quotient. Its source is the compact-test tensor product; its target is the
whole Schwartz/coefficient tensor product. No surjectivity of this map is
claimed. `integral_normalizedSectionTensor_eq_modelIntegral` extends the exact
pure-section comparison to every finite algebraic compact-test tensor by
linearity of both integrals. Section surjectivity then proves that every
coefficient of the identity integral belongs to the whole model-integral
image, simultaneously as a function of all ambient elements.

Whittaker covariance, nonvanishing of the common functional, and the reverse
inclusion for arbitrary Schwartz tests are further obligations. The module
proves no full image equality.
