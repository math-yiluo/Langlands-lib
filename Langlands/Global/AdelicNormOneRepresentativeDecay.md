# Weighted norm-one representatives and continuous cuspidal tests

`HasRapidDecayOnNormOneRepresentatives` is a bound for a function on the adelic
points of a group over a number field, for a supplied finite-dimensional
matrix representation and its adelic height \(H\). For every natural power \(m\) there is a
constant \(C\geq 0\) such that every norm-one point \(x\) has a rational
translate \(y=r x\) satisfying
\[
  |t(y)|H(y)^m\leq C.
\]
The rational translate may depend on \(m\) and \(x\). For a rationally
invariant function, weight zero gives a bound on all norm-one points.
This is the estimate needed from rapid decay on Siegel representatives
in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*,
I.2.12.

For a connected reductive group, the remaining results use a central
split torus comparison of the positive rational quotient with the
norm-one rational quotient, and right invariance of norm-one Haar.
`exists_cuspidalClass_of_bounded_normOneRestriction` starts with a
continuous rationally invariant cusp function whose norm-one
restriction is bounded. The norm-one quotient has finite volume, so
the transported restriction is square-integrable. Its class belongs
to the full cuspidal \(L^2\) space by the period transfer theorem.
The class agrees almost everywhere with the transported restriction.
For every compactly supported continuous kernel, the kernel-vector
unfolding proves that both representatives give the same partial
convolutions at all adelic points.

`normOnePartialConvolution_cuspidalClass` starts with a cuspidal \(L^2\)
class and a compactly supported continuous kernel. Evaluation through
continuous projected kernel vectors gives continuity of the partial
convolution. Rational invariance and vanishing of proper periods
follow from the corresponding partial convolution formulas. This is a
norm-one version of preservation of cuspidality under smoothing as in
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*,
I.3.4, printed pp. 45–46.
For a test function kernel and a positive-size closed matrix
embedding, `hasNormOneRepresentativeDecay_normOnePartialConvolution`
applies the uniform partial convolution decay proposition with a
singleton set of right factors to obtain the weighted bound.

Together these comparisons allow the two sides of the transpose
calculation in the norm-one Levi pairings to use either a continuous
cuspidal test or its Hilbert-space class. The pairing characterization
is Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, §6.2, equation (6.8).
