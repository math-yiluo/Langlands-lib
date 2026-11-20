# Rigidity of the scalar in the finite Cartan numerator

Suppose two numerators with the same complex and real slot counts and strictly positive
induced weights are proportional by nonzero constants. The constants and the numerator
functions then agree. This allows a scalar from the normalization of compact coordinates
to be attached to its original block list during the comparison.

Set all radial coordinates to zero, all real coordinates to the identity, and the complex
angles to the same variable. Every permutation then contributes the same product of
orientation differences, so the common multiplier is the product of the two permutation
counts. The Lean proof expands the product of differences by choosing an orientation in
each complex slot. The frequency of a choice is its signed sum of the induced weights.
Strict positivity makes the all-positive choice the unique one attaining the sum of all
weights. Its coefficient is one, and larger frequencies are absent.

The Fourier coefficient identity for the exponential modes gives zero above that sum and
`2π` at the sum for the product of differences. If the two sums of weights differed, the
coefficient at the larger sum would contradict proportionality by nonzero scalars. At their
common largest frequency, the permutation counts and `2π` cancel. Substituting the equal
scalars into the original identity gives equality of the entire numerator functions.

This is an internal consequence of the finite numerator expansion and the existing
exponential Fourier coefficient formula.
