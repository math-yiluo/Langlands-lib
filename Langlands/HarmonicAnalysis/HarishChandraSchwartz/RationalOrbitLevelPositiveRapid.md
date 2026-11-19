# Full-height rapid decay for the actual positive constant term

`RationalOrbitLevelPositiveRapid` is the original finite-seminorm estimate
for the half-modulus-scaled positive constant term on the proper positive
region. It uses the ambient Xi and the full matrix height of the supplied
matrix representation, and applies at every real order.

`rationalOrbitLevelPositiveRapid_of_exponential` starts from the
fixed-level exponential estimate with the literal Levi Xi. Multiplication
by the standard half modulus and the proved spherical comparison put
ambient Xi in the bound. The exponential estimate in the norm of `H₀`
then implies each power bound by `exists_exp_neg_le_rpow`. Minimal-Levi
Cartan covering bounds the full matrix height by a constant times
`1 + N(H₀)`. The height comparison for seminorms transfers the power
bound to that height, including negative orders. The set of derivative
indices stays finite and only the scalar in the estimate changes.

This is a derived step of the proper-region estimate in Waldspurger
VI.3.1. The exponential input is the uniform bound from the per-section
VI.2.3 theorem and the finite compact fiber tests.
