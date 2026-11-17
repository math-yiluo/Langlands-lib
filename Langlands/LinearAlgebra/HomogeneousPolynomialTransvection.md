# Determinants of elementary homogeneous polynomial substitutions

This is an internal continuation of the homogeneous substitution matrix and
its diagonal determinant computation. It uses Mathlib's coefficient formula
for multiplication by a monomial, block-triangular determinant theorem, and
`Matrix.diagonal_transvection_induction`. It adds no external source claim.

For polynomials over any commutative coefficient ring, `dvd_aeval_sub`
proves that generatorwise congruence of a substitution to the identity
modulo a polynomial `a` implies that congruence on every polynomial.
Its proof is by polynomial induction, with an explicit expansion of the
difference on multiplication by a variable.

`X_pow_succ_dvd_aeval_sub` treats a substitution that fixes `X_i` and
is congruent to the identity modulo `X_i`. If `p` is divisible by `X_i^k`,
the difference between its substituted value and `p` is divisible by
`X_i^(k+1)`. The proof factors `p = X_i^k q` and uses the preceding
congruence for `q`.
`X_pow_dvd_monomial` supplies the relevant divisibility for any monomial.
`coeff_eq_zero_of_X_pow_dvd` proves vanishing of a coefficient whose
`i` exponent is smaller than that divisor power.

For a transvection `T = 1 + c E_ij` with `i ≠ j`, `column_transvection`
computes the linear substitution: `X_j` becomes `X_j + c X_i`, and all
other variables stay fixed. In particular, `X_i` stays fixed and all
variables agree with their original values modulo `X_i`.
`representation_transvection_le` uses the divisibility improvement to
prove that every monomial coefficient whose `i` exponent does not increase
is exactly the coefficient of the identity action.

`det_representation_transvection` proves that the homogeneous substitution
matrix has determinant one over every commutative ring. The implemented
proof labels monomials by their exponent of `X_i`, regarded in the opposite
order. The coefficient computation proves block triangularity for these
labels and identifies every diagonal block with the identity. Mathlib's
block determinant formula finishes the proof.

Finally, `det_representation_field` proves that
`det(representation M d) = det(M)^(exponent σ d)` for every square matrix
over a field. The variable type is arbitrary finite, and singular matrices
are included. The proof applies Mathlib's diagonal/transvection induction:
the diagonal formula and the transvection determinant computation give the
generators, and the multiplicativity of `representation` gives closure
under products.
