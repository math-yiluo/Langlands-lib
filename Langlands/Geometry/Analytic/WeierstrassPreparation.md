# Preparation of normalized distinguished restricted series

Author: Worker 56.

The input is an actual restricted series over a complete, nontrivial,
ultrametric normed commutative ring with norm of one equal to one. Its
coefficient at the distinguished degree is one, all coefficients lie in the
unit ball, and all later coefficients have norm strictly below one.

The proof first establishes sharp norm bounds for every division
decomposition, not just the constructed one. It divides the actual monomial
of distinguished degree by the given series. Comparing this quotient with
division by the polynomial truncation proves that its difference from one
has norm strictly below one. A convergent geometric series therefore
constructs an actual unit. Subtracting the remainder from the monomial gives
the monic polynomial factor, whose coefficients lie in the unit ball.
Uniqueness follows from uniqueness of analytic
division; the argument includes distinguished degree zero.

This is the normalized, unit-radius case of Proposition 2.2.2 in the
retained Berkovich-course notes, pages 3–4. The proof constructs the unit by
a small-norm geometric series rather than using the notes' order function.
Leading-unit normalization is developed in `DistinguishedNormalization`.
Variable regrouping, coordinate changes, Noether normalization, and the
general quotient spectral power-bound theorem are developed in separate modules.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
