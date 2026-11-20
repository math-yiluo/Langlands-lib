# One-parameter holomorphic detection of specialization

Let \(E_t\) be a family of linear maps from a finite-dimensional complex
space into scalar functions. Suppose that the values \(E_t(v)(x)\) are
holomorphic on a common preconnected parameter set containing the
specialization point \(z\), and one \(E_{t_1}\) is injective there.
Then finitely many Taylor coefficients of \(E_t(s(t))\) detect \(s(z)\)
for every section with holomorphic scalar coordinates at \(z\).

Choose point evaluations and source coordinates making the matrix of
\(E_{t_1}\) the identity. The determinant is holomorphic, so nonvanishing
at \(t_1\) gives finite analytic order at \(z\). The entrywise formal Taylor
map preserves the determinant and the matrix-vector product. The determinant
order plus one gives a uniform coefficient bound by
`constantCoeff_eq_zero_of_mulVec`. The constant coefficients of the
section are its coordinates at \(z\).

For a holomorphic family on a ball in a complex normed space,
`exists_lineDerivativeDetectionOrder` uses the complex affine line through
the base point and any injective parameter in the ball. A disk about zero
containing \(1\) maps entirely into the ball. Applying the
one-parameter result on this disk produces the directional derivative
bound at the base point.

These are the detection arguments of R. P. Langlands,
*On the notion of an automorphic representation* (1979), Lemma 9, printed
p. 207, PDF p. 202 of Corvallis Part I
(`langlands-1979-notion-automorphic-representation`).
