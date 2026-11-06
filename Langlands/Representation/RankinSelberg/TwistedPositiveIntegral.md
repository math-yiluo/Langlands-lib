# Strictly positive equal-rank integrals at a contragredient twist

This internal consequence uses the actual quotient integrand and normalized
determinant weight. The field and the two representation carriers have
independent universes. `HasPositiveEqualRankIntegral` asserts that some nonzero
inverse-standard functional and some vectors give an absolutely convergent
integral at `s=-u` whose real part is strictly positive, with the indicated
quotient measure and row cutoff.

The first theorem starts from
`HasPadicTwistedPositiveCoefficients T π σ ψ u ℓ` and a nonzero supplied
standard functional `ℓ`. Both representations must be smooth. The measure
must be positive on nonempty open sets, and the row cutoff must take only
zero and one and equal one at the identity's last row. Actual convergence
at `s=-u` is an explicit hypothesis for every pair of coefficient vectors.

The proof unpacks the fixed inverse-standard functional and squared-norm
coefficient identities. It chooses a vector on which `ℓ` is nonzero and
its paired second vector. At every representative the equal-rank integrand
is the squared norm from the coefficient package multiplied by the cutoff.
Its real part is therefore nonnegative everywhere and strictly positive at
the identity coset. Smoothness supplies continuity of the quotient integrand
by `equalRankIntegrandContinuous`. The supplied convergence and full support
of the measure imply a strictly positive real integral. Commutation of the
real part with the integrable complex Bochner integral gives the stated
conclusion.

The second theorem replaces the convergence hypothesis with compact support
of every paired quotient integrand at `s=-u`, assuming the measure is finite
on compact sets. Continuity and compact support then prove the required
integrability.

All conclusions are derived from the imported coefficient identity,
continuity theorem and elementary integration properties. A compatible
quotient measure supplies positivity on open sets by the imported
`IsCompatible.isOpenPosMeasure`; that compatibility is not implicit in the
definition. The construction of compact quotient support, rational
continuation, poles and the host L-factor formula remain separate obligations.
