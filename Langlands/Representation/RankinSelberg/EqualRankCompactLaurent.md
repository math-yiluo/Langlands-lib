# Laurent continuation from compact quotient support

This internal derived unit concerns the actual equal-rank quotient integrals
with the residue-normalized determinant absolute value. The quotient measure
is arbitrary. Convergence on a right half-plane remains an explicit hypothesis.

A function with compact topological support has only finitely many possibly
nonzero determinant-slice integrals. The determinant-order map is continuous
into the discrete integers, so the image of that compact support is finite.
Outside this image the function vanishes on the entire slice, and hence the
slice integral is zero.

For an equal-rank integrand with compact support at spectral parameter zero,
the definition `compactSliceLaurent` forms the finite Laurent polynomial whose
coefficients are those slice integrals.
At every convergent parameter the published determinant-slice expansion sums
to the original integral. The sum has finite support, and evaluating the
Laurent polynomial gives exactly that finite sum. The Laurent embedding is
regular at every nonzero spectral point, so this equality supplies a rational
continuation. Uniqueness on a right half-plane identifies any other rational
continuation with the same Laurent image.

Combining this result with `MirabolicRowCompactSupport` proves Laurent
regularity for a row test vanishing at zero under the explicit mirabolic
compact-translate property and compact open right stabilizer. Applying these
support conditions to supercuspidal coefficients still requires the Kirillov
theorem. No assertion about pole occurrence or the full L-factor is made here.
