# Polynomial-cleared two-block coefficient assembly

This is an internal algebraic reduction using `TwoBlockDominantLaurentAlgebra`
and Mathlib polynomial algebra. Its block equations and lower Fourier
coefficient law are explicit premises. It supplies no analytic block equation,
no identification of normalized generators, and neither final dominant-rank
target.

`laurentReflection_toLaurent` identifies finite Laurent reflection with the
explicit substitution `Polynomial.eval₂ C (C q⁻¹ * T (-1))` used in
`TwoBlockFirstBlockLaurentIdentityStatement`. Polynomial ring-homomorphism
extensionality reduces the proof to constants and the variable.
`laurentReflection_eval₂` follows from the involution.

`inverseReflectedMonomial q c d` is the monomial
`c⁻¹ q^d X^d`. Its product with the reflected monomial
`c q⁻d X⁻d` is one. The proof multiplies the constant coefficients and adds
the integer exponents, using that `c` and `q` are complex units.
`clearedProductMultiplier q c₁ d₁ c₂ d₂` is
`c₁ c₂⁻¹ q^d₂ X^(d₁+d₂)`. The multiplication formula expresses it as
the first monomial times the inverse of the reflected second monomial.

`twoBlock_cleared_comp` assumes two polynomial-cleared block equations and
the lower coefficient law `bD(-k) = q^(-k) b(k)`. It identifies `bD` with
the bilateral reflection of `b`, reflects the second equation, and uses the
cleared composition lemma to eliminate the common lower series. The result
retains the product of both reflected dual polynomials on one side and the
product of both original polynomials on the other.

`twoBlock_monomial_cleared_comp` specializes the two multipliers to nonzero
monomials and uses their proved inverse law to move the reflected second
monomial to the other side. It states the resulting identity using the
explicit polynomial substitution and `clearedProductMultiplier`. Both
polynomial factors remain; only a monomial with a proved inverse is removed.
This is valid for arbitrary bilateral series without a support restriction.

An analytic assembly must still supply the two block identities for actual
sections and compatible supplied measures, their common coefficient law,
and the identifications of all polynomial and monomial witnesses.
