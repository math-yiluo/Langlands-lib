# A common center ideal for the integrated induced action

`InducedConvolutionUniformCenterReductionStatement` assumes the ambient center conjugation
identity and an unnormalized restriction comparison at the identity. The latter gives a map
on smooth slices that evaluates by restriction along the Levi inclusion, and a transfer of
ambient central operators to Levi central operators that intertwines the actions on left
radical-invariant slices. The conclusion is a single cofinite center ideal annihilating the
smooth infinite slices of the integrated action for every complex parameter.

## Implemented proof

Choose the Levi operator transfer at the identity. Right translation intertwines the
ambient enveloping action with its adjoint conjugate. Since the ambient center is fixed
under this conjugation, the same transfer compares the action on every translated
Levi restriction. Translating a left radical-invariant slice preserves that invariance.

At each fixed finite coordinate, the adelic radical invariance of the input implies the
archimedean radical invariance of the ambient slice. Consequently, for an element `z` of the
input annihilator, the image of `z` under the fixed transfer kills every raw
Levi slice of the input. `inducedConvolutionLeviAnnihilator` shows that this same Levi
operator kills the corresponding output slices for every parameter. The left radical
invariance of the output follows from Iwasawa height covariance. Apply the center
comparison to the output and evaluate at the Levi identity. As the translate varies, this
proves the ambient differential vanishes at every archimedean point of each finite slice.
The cofinite annihilator can therefore be taken to be the input ideal itself.

## Provenance

This is an internal application of `infiniteSliceRightTranslationCovariance` and
`inducedConvolutionLeviAnnihilator`. The unnormalized comparison premise comes from the
parabolic center comparison specialized to the identity translate. Mœglin and Waldspurger,
*Spectral decomposition and Eisenstein series*, I.2.17, printed pp. 37–38, use the
parabolic center comparison with normalized Levi restriction. In the integrated action
the exponential of the Iwasawa height increment is invariant under left parabolic
multiplication, so the same unnormalized comparison applies at every parameter.
