# Convolution weights for invariant real height majorants

This internal analytic adapter permits a real auxiliary height in the
convolution estimates. It does not require that this height come from a
matrix representation, and does not assert that the original matrix
height is invariant under the chosen compact subgroup.

`IsConvolutionHeightMajorant K σ₀ σ` means that `σ` is nonnegative,
continuous, subadditive, left invariant under `K`, and pointwise at least
`σ₀`. The predicate includes no Xi estimate or integrability claim.

`SquareIntegrableWeight.mono_height` proves that a weighted Xi-square
estimate for `σ₀` remains true for a pointwise larger height `σ`, provided
`σ₀` is nonnegative. Keep the same natural exponent `d`; its negative is
nonpositive, so `(1 + σ)^(-d) ≤ (1 + σ₀)^(-d)`. Multiply by `Ξ²` and use
monotonicity of the nonnegative lower integral.

On actual rational points of a connected reductive group over a
nonarchimedean local field, fix a maximal split torus, generic cocharacter
and compact open Iwasawa subgroup `K`. For any nonempty finite matrix
representation `ρ`,
`rationalConvolutionWeights_of_heightMajorant` constructs the full
`ConvolutionWeights` for the actual `rationalXi` and any
`IsConvolutionHeightMajorant K (rationalHeight ρ) σ`, assuming the local
`SquareIntegrableWeight` for the original matrix height.
No closedness of `ρ` or Haar property of the measure is required once
this square estimate is supplied.

The proof uses the published positivity, continuity, compact invariance,
inverse symmetry and averaging identity for actual Xi. Subadditivity and
nonnegativity of the auxiliary height give the multiplicative height
inequality in `ConvolutionWeights`. Its continuity and compact invariance
are the corresponding assumptions of the majorant predicate.
The height-monotonicity theorem supplies the remaining square estimate.
There is no premise that `ρ(K)` lies in integral matrices.

Constructing a suitable invariant majorant and comparing its decay
seminorms with those of the original Schwartz space are separate inputs.
The compact supremum height is a possible consumer of this adapter; this
module does not assume its construction or publication.
