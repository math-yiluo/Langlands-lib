# Uniform evaluation of smoothed cuspidal \(L^2\) vectors

`groupSchemeFullAEL2CuspidalUniformConvolutionBound` proves
`GroupSchemeFullAEL2CuspidalUniformConvolutionBoundStatement`.
The proof uses the statement's own objects at its universe: the full cuspidal
subspace `fullAEL2CuspidalSubmodule`, the integrated right action
`fullAEL2CuspidalIntegratedAction` for the Haar measure on the adelic points,
the positive rational quotient with `positiveRationalQuotientHaarMeasure`,
and the input Hilbert norm.

## Continuous representatives

Fix a test kernel `f` and a cuspidal vector `φ`. The pointwise smoothing
`positiveQuotientLpSmoothing T i f φ` of the \(L^2\) class is formed from its
locally integrable pullback to the adelic group
(`locallyIntegrable_positiveQuotientLpPullback`). The convolution
differentiation theorem `adelicRightConvolutionDifferentiation` makes it
smooth, hence continuous. It is invariant under the positive rational
subgroup (`positiveQuotientLpSmoothing_invariant`), so it descends to a
continuous function `v` on the quotient, and
`positiveQuotientLpSmoothing_ae_eq` identifies `v` almost everywhere with the
integrated class `R f φ`.

## Boundedness of each smoothed vector

`positiveQuotientLpSmoothing_globalGrowth` gives a single exponent `m` such
that every archimedean derivative word of every smoothed vector is bounded by
a constant times the `m`-th power of the adelic height times the input norm.

The integrated operator preserves the full cuspidal subspace, so
`groupSchemeFullAEL2ContinuousCuspidality` shows that the pullback of the
continuous representative to the adelic group, which is the smoothed vector,
lies in the normalized parabolic cuspidal subrepresentation: its constant term
along the radical of every proper rational parabolic, for the normalized
quotient measure, vanishes at every adelic point.
`hasZeroProperParabolicConstantTerms_of_normalized` uses the equality of
radical images (`properRationalParabolicRadicals_eq`) to turn this into the
vanishing of the represented constant terms required by the rapid-decay
theorem.

The affine linear embedding theorem `affineLinearEmbeddingStatement` and the
positive-size replacement `exists_positiveMatrixEmbedding_of_isClosedSubgroup`
give a closed matrix embedding of positive size, which defines the height.
The norm-one rapid-decay theorem `adelicNormOneCuspidalRapidDecay` supplies a
subset of the norm-one subgroup that meets every rational left orbit there,
and, at decay exponent zero, a bound for the smoothed vector on that subset.
For an arbitrary adelic point `x`, `normOneProjection` gives a norm-one point
with the same class in the positive rational quotient
(`positiveQuotientHomeomorph_mk`), and a rational translate of it lies in the
subset. Rational invariance then bounds the smoothed vector at `x`. Each
smoothed vector is therefore bounded on the whole adelic group, with a bound
that may depend on the vector.

## Uniformity by Banach–Steinhaus

At each adelic point `x` the quotient convolution kernel
`quotientConvolutionKernel` supplies an \(L^2\) vector whose inner product with
the input is the pointwise smoothing at `x`. Composing with the isometric
inclusion of the cuspidal subspace into the ambient \(L^2\) space gives a
continuous linear evaluation functional on the cuspidal subspace. The
previous section shows that these functionals are pointwise bounded. The
cuspidal subspace is closed, hence complete, so `banach_steinhaus` gives one
bound `C` for all their operator norms. With the constant `max 0 C`, every
quotient point `q` lifts to an adelic point and `‖v q‖ ≤ C * ‖φ‖`.

## Source correspondence

Getz–Hahn (2024), Lemma 9.3.3 and estimate (9.13), printed pp. 247–248
(PDF pp. 259–260), state the uniform bound \(\|R(f)\varphi\|_\infty \ll_f
\|\varphi\|_2\) on the cuspidal space that feeds the trace-class argument.
The book derives (9.13) in the number-field case from Proposition 9.4.7,
printed p. 257 (PDF p. 269), whose Siegel-set estimate already carries the
factor \(\|\varphi\|_2\). The Lean proof takes another route: it uses only the
boundedness of each individual smoothed vector, given by the norm-one form of
the rapid decay of Theorem 9.6.4, printed p. 264 (PDF p. 276), and recovers
the linear dependence on \(\|\varphi\|_2\) from the uniform boundedness
principle applied to the kernel evaluation functionals.
