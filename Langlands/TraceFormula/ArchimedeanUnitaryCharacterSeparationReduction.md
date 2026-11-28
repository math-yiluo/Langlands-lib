# Archimedean character separation from trace class

`archimedeanUnitaryCharacterSeparation_of_traceClass` derives the full character
separation statement from trace class of smooth integrated operators, in the
universes of the summand and target Hilbert spaces separately. Uniqueness of the
vectorwise Bochner integral identifies the tested operators with those supplied
by the trace-class theorem.

The trace of the autocorrelation is the sum of squared norms of the images of
a Hilbert basis. A normalized smooth test has nonzero integrated image on a target
basis vector, so an autocorrelation has positive target trace. Unitary
equivalence preserves the traces by rectangular cyclicity. The positive test
then gives summability of the coefficients in the equivalent class. Subtracting
that class leaves a residual scalar times the target trace.

For the remaining indices, the coefficient-weighted basis images give a vector
in a Hilbert sum at each test. Its squared norm is the sum of the absolute
weighted autocorrelation traces. If the residual scalar were nonzero, the
triangle inequality at autocorrelations would give a uniform norm bound on the
integrated image of the target basis vector by the Hilbert-sum norm. Joint
translation holds for these two test-space maps by left invariance. A nonzero
bounded intertwiner between irreducible unitary representations normalizes to a
surjective isometry by Schur's lemma and closed-range irreducibility. Each summand indexed by the complement of the equivalent class therefore has
only the zero bounded intertwiner to the target. The
Hilbert-sum domination theorem forces the target map to vanish and contradicts
the chosen nonzero test. The residual scalar is zero, and a nonzero equivalent
class sum implies that the class has an index.

This implements the domination argument in the remark to Jacquet–Langlands,
*Automorphic Forms on GL(2)*, Chapter 3, §16, p. 261 (PDF p. 265), in the setting
of the published archimedean separation statement.
