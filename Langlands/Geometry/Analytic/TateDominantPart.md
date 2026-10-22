# Finite dominant part of a Tate series

Author: Worker 56.

`coefficientPart` is the genuine finite sum of the selected coefficient
monomials. Its coefficients are exactly the selected coefficients of the
original series, and its norm is no larger. The remainder has norm strictly
below a positive threshold whenever every coefficient at or above the
threshold was selected. The proof uses attainment of the remainder's
coefficient supremum; it does not infer a strict supremum bound from pointwise
strict inequalities alone.

`dominantExponents` constructs a suitable finite set directly from
restrictedness. At the norm of a nonzero series, this set is nonempty because
the norm is attained. No field structure or completeness is needed.

This supplies the finite dominant-coefficient decomposition used in the
retained Berkovich-course notes, Section 2.2, Proposition 2.2.5, page 4. It is
a supporting construction, not the coordinate-distinguishedness or quotient
spectral power-bound theorem.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
