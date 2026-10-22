# Product Haar measure in block unipotent coordinates

Author: Worker 117.

The closing theorem
`Langlands.glBlockUnipotentCoordinateHaarStatement` proves exactly the published
`Langlands.GLBlockUnipotentCoordinateHaarStatement`, for every field universe,
p-adic field, supplied topological realization and ordered block shape.
For any family of additive Haar measures on the strict upper rectangular
blocks, their product pushes forward under the inverse block-coordinate map
to a multiplicative Haar measure on the actual unipotent radical. The block
and radical measurable structures are precisely the Borel structures specified
by the unchanged statement; the coordinate source has the dependent product
measurable structure. There is no extra countability, sigma-finiteness,
normalization or triangular-invariance hypothesis in the closing theorem.

## Implemented proof

For a fixed radical element `a`, define the correction at coordinates `X` to
be the coordinates of `a * coordinates.symm X` minus `X`. The published
`radicalCoordinates_mul` formula cancels the variable block `X_ij`, leaving
`a_ij + sum_{i < k < j} a_ik X_kj`. The private lemma
`coordinateCorrection_depends` proves that this correction depends only on
blocks of strictly smaller natural-number gap: `j - k < j - i` whenever
`i < k < j`. Equality of the correction follows term by term in the finite
sum, followed by additive cancellation.

The generic theorem `coordinateLeftTranslation_preserving_of_triangular`
works over a second-countable topological commutative ring, with Borel
measurable structures on the rectangular blocks. Continuity of multiplication,
subtraction and the coordinate homeomorphism makes the correction measurable.
It applies the finite triangular translation proposition with rank `j - i`.
Adding the original coordinate back to its correction identifies the resulting
map with left multiplication expressed in block coordinates. This proves
preservation of the finite product of any sigma-finite additive left-invariant
block measures. Matrix second countability is obtained from their finite
function-space realization; it also identifies the product measurable
structure with the Borel structure where needed.

The generic theorem `coordinateHaar_of_triangular` additionally assumes that
the block measures are additive Haar measures. The product is finite on
compact sets and positive on nonempty open sets. The inverse coordinate
homeomorphism transports these properties to the radical. To prove left
invariance there, the proof composes pushforwards and uses the identity
between left multiplication after inverse coordinates and inverse coordinates
after coordinate left translation. The product-preservation result then
supplies the required equality. These three properties assemble the
`IsHaarMeasure` instance for the transported measure.

The p-adic theorem `glBlockUnipotentCoordinateHaarStatement_of_triangular`
installs the supplied topology and local-field structure. Intrinsic second
countability is supplied by `T.secondCountableTopology` from the published
`PadicScalarHaarScalingProof` module. Finite rectangular matrix spaces are
locally compact and second countable. Their additive Haar measures are
therefore sigma-finite, discharging the generic helper's measure hypothesis.
It then applies the generic Haar-transport theorem.

Finally, `glBlockUnipotentCoordinateHaarStatement` discharges the triangular
proposition using the published
`Langlands.HarmonicAnalysis.finiteTriangularTranslation`, with the finite
upper-pair index universe specialized to zero and the coordinate universe left
arbitrary. The intermediate helpers expose their triangular premise for reuse;
the closing theorem has exactly the original unconditional proposition type.
All finite-product arguments include the empty index type, so the trivial
radical cases, including rank zero and one block, are retained without an
extra case hypothesis.

## Provenance and scope

This is an internal application of the published block-coordinate multiplication
formula and homeomorphism, the published finite triangular translation theorem,
and Mathlib's finite-product and Haar-measure transport results. It is not a
transcription of an external theorem. The Lean imports the existing statement
and its dependencies without changing their paired files. This module proves
the coordinate-Haar prerequisite; the determinant scaling and arbitrary-Haar
uniqueness argument needed for the block modulus theorem are separate results.
