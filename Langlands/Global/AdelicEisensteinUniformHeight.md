# Uniform polynomial bounds for Iwasawa height increments

`IsIwasawaCompact.exists_uniform_heightPower_mul_le` bounds the power at `x * g` by the
absolute value of the power at `x` times a polynomial weight in `g`. Both the exponent and the
multiplicative constant work for all parameters in a bounded set of complex coordinates.

Using a real basis of the coordinate space, the proof puts the parameter set in a box. For
fixed `x` and `g`, the logarithm of the ratio of the two absolute values is a real-linear
functional of the parameter. Choosing each coordinate sign according to that functional gives
an upper bound at one vertex of the box. Apply the fixed-parameter polynomial bounds from
`iwasawaHeightPowerPolynomialBound` at the finitely many vertices. The sum of their nonnegative
exponents is a common exponent because the normalized matrix height is at least one.

This finite-dimensional argument extends the fixed-parameter estimate in
`AdelicHeightPowerPolynomialBound`. The underlying source comparison is the polynomial
character bound in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.2.2(v), p. 20. The registered source `moeglin-waldspurger-1995-spectral-decomposition`
contains `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
