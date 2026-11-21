# Normalization of compact cuspidal block evaluations

An unnormalized block Lie evaluation sends the derivative of an upper
triangular direction to the sum of its diagonal block operators acting
on the original coefficient tensor. This is the equation recorded by
`IsUnnormalizedBlockLieEvaluation`.

The finite normalized cuspidal coefficient equivalence is the tensor
product of the inverse half-modulus twist equivalences. In a single
slot a Lie operator transported through the equivalence is the new
slot operator plus the scalar trace correction. The proof uses
`PiTensorProduct.map_comp` and the linearity of the tensor map in that
slot to transport this identity from the factor to the tensor. Summing
the trace corrections gives `blockHalfDifferential`. This proves
`IsNormalizedBlockLieEvaluation` for the very same coefficient
equivalence used for finite parabolic covariance.

The inverse half-modulus twist is one on each compact block, so the
coefficient equivalence also transports both compact evaluation
equations without an additional scalar.
