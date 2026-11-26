# Parabolic covariance and moderate growth of adelic induced convolution

`Langlands.Global.AdelicGroupPoints.InducedConvolutionParabolicCovarianceStatement` gives
left invariance of the integrated induced action under `U(𝔸)M(F)` and equivariance under the
split component with the half-modulus character, when the input has those properties. The
module also proves that a continuous compactly supported kernel sends a moderately growing
input to a moderately growing output at each complex parameter.

## Implemented proof

The height factors in the induced translate combine to the exponential of the height
increment `H_P(g h) − H_P(g)`. Left multiplication by a point of `P(𝔸)` adds the same
character logarithm to both heights. Consequently a left covariance factor of the input is
preserved in the translate and comes out of the Haar integral. Both the unipotent and the
rational Levi images lie in the parabolic image, so their join does as well. The split
component maps into the same parabolic image through the Levi.

By Iwasawa decomposition, every height increment for right translation by a point of
a compact set `C` is the height of a point of `K · C`. Continuity gives a uniform bound on
the corresponding exponential factor for a fixed complex parameter. For moderate growth,
the proof uses this bound with `C` the support of the kernel and the Library's uniform
polynomial growth bound on compact families of right translates. It integrates the bound
against the absolute value of the kernel. For a matrix representation of positive dimension,
the normalized height is a positive scalar multiple of the source norm. For dimension zero,
the height is constant, and the proof uses exponent zero.

## Provenance

The covariance and growth estimates are from the parabolic covariance of the Iwasawa
height and the induced action of J. Arthur, *An introduction to the trace formula*, §7,
printed pp. 32–33 (PDF pp. 44–45). The volume is registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`. The Library places
the half-modulus in the inducing function. The estimates give the covariance and growth
parts of the proof described in `AdelicInducedConvolutionFiniteSpanStatement`.
