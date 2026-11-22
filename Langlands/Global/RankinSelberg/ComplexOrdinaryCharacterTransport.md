# Change of additive character for ordinary complex normalized tests

`complexOrdinaryCharacterTransport` proves the transfer of covering and
finite-sum families stated in `ComplexOrdinaryCharacterTransportStatement`.

The ordinary equal-rank quotient substitution takes a standard-character test
at the transported quotient measure to a test for trace parameter `a` at the
given quotient measure. The same left change of variables acts on both
Whittaker functions. The last row is preserved, so the Schwartz test is
unchanged. The entire determinant multiplier is nonzero and transfers
pointwise coverage. For `‖a‖ = 1` the multiplier is one, so a finite sum of
normalized values equal to one transfers as well.

For unequal ranks the larger coefficient needs a right translation in addition
to the left change of character. The larger diagonal conjugates a padded
matrix to the padding of its conjugate by the smaller diagonal. Multiplying on
the right by the inverse larger diagonal times the padded smaller diagonal
then matches the ordinary padded argument exactly. Substitution on the
smaller quotient gives the identity for the two ordinary integrals, with the
inverse determinant power as multiplier. At unit-norm scales the right
correction is unitary and preserves the finite Whittaker model. The
determinant multiplier is then one, so both coverage and finite-sum
generation transfer at those scales. In particular the standard character
with parameter `-1` inherits the finite sums at parameter `1`.

These are derived change-of-variables lemmas for Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), Remark 2.2, author pp. 7–8, applied to the
ordinary integrals (2.4) and (2.6), p. 6. The transported compatible quotient
measure absorbs the Haar rescaling.
