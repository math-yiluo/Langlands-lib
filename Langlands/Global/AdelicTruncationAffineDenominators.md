# Affine coroot denominators in spectral coordinates

The generic region for a fixed affine label list is the complement
of the union of the coroot denominator zero sets. For a nonvanishing
affine function on a real normed space, each open neighborhood of a
zero contains points along the line toward a nonzero value. Along that
line each positive step gives a nonzero value. This proves density
for each single denominator. Applying the finite intersection argument
in complex coordinates over \(\mathbb R\), and again after the
real-linear imaginary slice, gives the open dense loci in
`affineNonzeroRegion_open_dense`.

The index `AffineCorootIndex` lists the standard parabolic, its label,
and its relative simple coroot. `affineCorootLinear` and
`affineCorootOffset` express the actual coroot value by a complex linear
form and a constant. The equality `preimage_genericParameterRegion`
identifies the resulting locus with the published generic region in
the chosen chart. `open_dense_genericParameterRegion` applies the
affine argument when every coroot denominator has a nonvanishing
witness on the imaginary slice.

For the analytic continuation argument, a finite product of affine
factors can include repeated copies of a factor. At an imaginary
point, split the product into factors that vanish there and factors
that are nonzero there. The latter product stays nonzero on an open
neighborhood of the point, and dividing the cleared holomorphic
numerator by it leaves a holomorphic numerator. Each vanishing factor
equals its linear part applied to the difference from the center.
Its nonvanishing witness on the imaginary slice, after subtracting the
center, shows the real restriction of the linear part is nonzero.
When those restrictions are real-valued, this constructs
`HasImaginaryHyperplanePresentation` for local hyperplane removal.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 25 and 32, (7.12) and
the final step of the proof of Theorem 7.1.
