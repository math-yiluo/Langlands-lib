# Compactly supported integration of finite wave-packet sums

`symmetricWavePacketConvolution_of_finiteExpansions` proves convolution
stability of the symmetric packets from finite expansions for normalized
convolution and intertwining, the continuity and covariance of the
specified Eisenstein continuations, and the existence of imaginary-axis
continuations for the new inducing forms.

The sum on the adelic group uses a continuous compactly supported scalar
coefficient for each inducing form and jointly continuous imaginary
Eisenstein values. `continuous_wavePacketSumOnGroup` applies the continuity
of a parametrized integral with common compact support. The support can be
chosen as the union of the supports of the finitely many coefficients in
that component. The quotient descent uses
`wavePacketSumOnGroup_leftRationalInvariant` and the left rational invariance
of the individual Eisenstein values.

`rightConvolution_wavePacketSumOnGroup` applies Fubini to the spectral and
adelic integrals. For each component the product integrand is continuous
and supported in the product of the kernel support and the union of the
coefficient supports. The two measures are finite on compact sets. Linearity
of integrable finite sums then gives the convolution on each Eisenstein
value, with the original reciprocal Weyl-set weights.

The new inducing family at a parabolic is indexed by pairs of an input
form and an index in its finite convolution expansion. Each new scalar
coefficient is the input coefficient multiplied by the corresponding
entire coefficient restricted to the imaginary axis. The finite
intertwining comparison puts this presentation in the symmetric space
for the same supplied operators. The new Eisenstein continuations are
chosen for this finite family with a common holomorphy domain at each
parabolic. Restricting the family to the expansion of an individual input
form lets the continued covariance identify its convolved Eisenstein
value. Reindexing the integrand then gives the new packet sum. In matrix
size zero the adelic group is a subsingleton, so convolution simply
scales the input family by the integral of the kernel.

`wavePacketTranslation_of_analyticInputs` combines this construction
with the quotient approximation argument. It uses the Gram identity
for the \(L^2\) membership of the packets and the left-finite
test-function separation property for the right regular action. Its
conclusion is the `WavePacketTranslationStatement` on the full rational
quotient.

This is the integration step in applying the covariant action to Arthur's
finite packet formula in *An introduction to the trace formula* (2005),
§7 pp. 34–35 (volume PDF pp. 46–47), registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
