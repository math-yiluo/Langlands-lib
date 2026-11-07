# Proof of centered block L-polynomial rescaling

`centeredBlockLPolynomial` proves `CenteredBlockLPolynomialStatement`.
It uses the published two-variable real-twist theorem
`IsPadicRankLPolynomial.twist_real`, whose successor-rank specialization is
the symmetric L-polynomial relation.

The two successive polynomial substitutions compose to the substitution
with the sum of the two real exponents, by the complex-power addition law.
The sum for the centered indices is `blockExponent / 2`. The integer-power
law for complex powers identifies this substitution with the stated power
of `centeredHalfShiftUnit`.

For the dual certificates, inverse transpose replaces the determinant norm
by its inverse, so the real-power exponent changes sign on the same
underlying representation space. The representation identity is a direct
specialization of the published
`Parabolic.inverseTransposeDeterminantTwist`. The same twist theorem applies to the
supplied dual base certificate using `negatedSelfDualHaar`, whose underlying
measure is exactly the original one. The two negated exponents give the
negative of `blockExponent`.

The additional scalar lemmas show that the half-step unit squares to the
canonical residue reflection and has norm at most one. The linear-factor
and finite-product lemmas state how polynomial rescaling multiplies the
reciprocal-root parameters. All are internal consequences of the existing
spectral substitution and centered-block definitions; no segment-component
formula is assumed.
