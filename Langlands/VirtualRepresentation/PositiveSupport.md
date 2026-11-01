# Support and effectivity for positive integral maps

Author: Worker 165.

This internal algebraic derivation concerns finitely supported integral
vectors on arbitrary basis types in independent universes. It asserts no
representation-theoretic positivity or Jacquet detection theorem.

`PositiveSupportStatement` combines two implications. First, if an integral
endomorphism sends every basis vector occurring in an effective vector `v`
to an effective vector, and sends `v` to a natural-number multiple of
itself, each of those columns is supported in the support of `v`.
Second, for an integral map between possibly different bases, assume its
columns on the support of an effective vector `v` are effective and
nonzero, and every coefficient of the image of `v` is at most one. The
map then reflects effectivity for vectors supported in `v`.

`linear_apply_coefficient` expands a coefficient of an image as the finite
sum of the positive-weighted columns. `weighted_column_le` bounds each
term by this sum. The support implication follows because a positive
column coefficient outside the support would force a positive coefficient
of the total image there.

For the reflection implication, `exists_isolating_coordinate` chooses a
nonzero coordinate of one column. The integer weights and column
coefficients are positive at that coordinate. Their product is at most
one, forcing both to equal one. The remaining nonnegative terms have
sum zero, so every other supported column vanishes there. Evaluating the
image of any vector supported in `v` at this coordinate recovers exactly
the coefficient of the chosen basis vector. Effective image coefficients
therefore imply effective original coefficients.

The proof uses finite sums, the existing concrete integral-lattice basis
and elementary ordered-integer arithmetic. It requires neither a
classification of representations nor any assertion that a particular
representation-theoretic map has the displayed positivity,
multiplicity-free image or nonzero-column properties. Applications must
establish all those hypotheses independently.
