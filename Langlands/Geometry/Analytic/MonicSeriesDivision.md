# Division of convergent series by monic polynomials

Author: Worker 56.

The construction divides each polynomial truncation of a restricted series
by a monic polynomial with coefficients of norm at most one. The sharp
finite polynomial estimates show that both resulting sequences are Cauchy
in the actual Gauss norm. Completeness supplies their limits. Continuity of
coefficient maps makes every high coefficient of the remainder limit zero,
so this limit is its polynomial truncation of the required degree.
Continuity of multiplication and addition proves the division equation.

To prove the sharp estimates and uniqueness, the file first approximates an
arbitrary possible quotient by polynomials. The finite division bounds pass
to the limit. Applying those bounds to the difference of two decompositions
forces both differences to vanish.

The hypotheses are a complete ultrametric normed commutative coefficient ring
which is nontrivial, and an actual monic polynomial with unit-ball
coefficients. There is no field assumption or multiplicative norm assumption.
This is the monic polynomial stage of the analytic Weierstrass argument in
the retained Berkovich-course notes, Section 2.2, page 3. Division by a general
distinguished series, preparation and Noether normalization are not supplied
by this file.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
