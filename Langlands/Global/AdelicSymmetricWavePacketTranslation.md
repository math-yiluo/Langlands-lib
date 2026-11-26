# From symmetric convolution stability to wave-packet translation

`wavePacketSumOnGroup` uses the same coefficients, spectral measures and
reciprocal Weyl-set weights as `wavePacketSum`. Evaluating the former at a
chosen quotient representative gives the latter.

`SymmetricWavePacketConvolutionStatement` uses the exact finite-family data
of `WavePacketTranslationStatement`. It asks for continuity and left-rational
invariance of the packet on the adelic group. It also asks that convolution
with a left-finite test function be a packet with a smooth finite presentation
in the same symmetric family space, with admissible Eisenstein continuations.

`wavePacketTranslation_of_convolution` proves the implication
`WavePacketTranslationOfConvolutionStatement`. The Gram premise gives
square integrability of the original packet and of every convolved packet.
The separation premise then gives an error bound for one test convolution
via `leftFiniteConvolutionApproximation`. The convolution premise produces
its finite symmetric data. Left invariance identifies the original packet
at the chosen representative of the translated coset with its value at the
translated adelic point. This yields the exact quotient `eLpNorm` inequality.

The implication uses the right action on the actual Haar quotient and the
fixed-family convolution premise. It is an internal reduction of the
translation part of Arthur, *An introduction to the trace formula* (2005),
§7, pp. 34–35 (volume PDF pp. 46–47), registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
