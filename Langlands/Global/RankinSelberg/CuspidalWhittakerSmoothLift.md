# The actual cuspidal Whittaker lift to smooth archimedean functions

Let `F` be a number field in an arbitrary universe whose additive adele
quotient is compact. Fix an actual cuspidal operator realization `T` of
`GL_(r+1)`, an additive character `ψ` satisfying
`IsStandardAdditiveCharacter`, and a finite adelic argument `b`.
`whittakerSmoothLift` collects the Library's linear Whittaker evaluations
of a vector `v : T.Space` into a smooth scalar function on the infinite
adelic group. Its exact value at `a` (`whittakerSmoothLift_apply`) is
`cuspWhittaker F T ψ v` at the adelic point whose infinite coordinate is
the mixed matrix coordinate of `a` and whose finite coordinate is `b`.
This is the original integral, not a replacement coefficient. Smoothness
follows by restricting the published `contDiffOn_archWhittakerExt` to the
invertible mixed matrices and identifying the restriction with that
integral.

In the mixed coordinates, a real direction `X` corresponds to a matrix
`Z = realLieAlgebraToMatrix F (r + 1) X`. The invariant differential at a
unit `g` is computed in direction `g * Z`. The published
`fderiv_archWhittakerExt_mul` identifies it with the integral on
`lieDeriv T Z v`. The inverse coordinate map inside `matrixGenerator`
identifies this vector with the action of the complexified real generator
of `X` on `v`. The linear covariance lemma
`envelopingCovariance_of_realGenerators` then gives
`whittakerSmoothLift_envelopingAction`: the lift intertwines the
enveloping action of `T.realization` with the smooth-function action for
every complex enveloping operator.

This is an internal construction from the existing Whittaker integral and
its mixed-matrix regularity. It does not identify the integral with a
Hilbert orbit evaluation or prove multiplicity one.
