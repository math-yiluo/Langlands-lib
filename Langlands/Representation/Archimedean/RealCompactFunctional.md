# A functional on the real compact model

The compound matrix action becomes diagonal for rotations written in the
paired eigenbasis. Each basis vector has one mode on each rotation plane.
Its frequency is the difference of the counts of the two rows, since the
row eigenvalues are opposite exponential modes. A gain constant on a pair
acts by its value raised to the sum of the two counts. These eigenvalue
formulas follow by counting each diagonal entry once for every occurrence
of its row.

The sign and Fourier conditions force any eligible form to be supported on
the canonical configurations. Fourier orthogonality rules out frequencies
with absolute value below the pair weight minus one. The half-turn sign
rules out that boundary because the sum and difference of two row counts
have the same parity. A singleton prescribed to occur once must occur at
least once, by its sign. The row-count saturation theorem now identifies
every configuration on which the form is nonzero.

The constructed form sums the base-coordinate evaluations after all row
exchanges. Composing with an exchange reindexes this sum. Only the identity
exchange contributes on the all-true basis vector, where the form is one.
The form is supported on the canonical configurations, so the diagonal
formulas give gain covariance and Fourier vanishing. Each canonical
basis vector is a nonzero multiple of a row exchange of the all-true
basis vector. Thus any form with the given invariance, elementary signs
and Fourier vanishing is determined by its value on that vector.

This construction is internal to the formal compact model. It uses
`RealCompactRows.exists_eq_target`, `CompoundMinorProduct.action_diagonal`
and `CompoundMinorProduct.exists_action_perm_single` from the paired
helper modules, and `RealBlockFourierFinite.coeff_expMode` for Fourier
orthogonality.
