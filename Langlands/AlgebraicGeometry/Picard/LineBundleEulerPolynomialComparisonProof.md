# Comparing twisted Euler polynomials

Let `p` and `p'` be the structure maps of smooth proper geometrically
connected schemes of the same relative dimension `g` over possibly
different fields. Let `L` and
`L'` be ample line bundles, and let `N` and `N'` be arbitrary line bundles
on the respective schemes. The two sequences are the actual Euler
characteristics of `N ⊗ L^n` and `N' ⊗ L'^n`.

`coherentEulerPolynomial_eq_of_eventually_sq_eq` shows that agreement of
the squares for all sufficiently large integers `n` implies equality of
the two actual twisted Euler polynomials in `ℚ[X]`. Its type is exactly
`CoherentEulerPolynomialSquareComparisonStatement`. The theorem
`Rosati.MumfordTraceReduction.euler_facts` evaluates each polynomial at
`n` and identifies its coefficient of degree `g` with the coefficient of
the pure Euler polynomial of its ample twisting bundle.
`RationalPolynomial.eq_of_eventually_nat_eval_eq` identifies the polynomial
squares. Equality up to sign follows over the domain `ℚ[X]` and
`lineBundleEulerPolynomial_topCoeff_pos` gives positive coefficients of
degree `g` for both polynomials, forcing the positive sign.

When the coefficient bundles are pullbacks by endomorphisms of abelian
schemes over algebraically closed fields, `Rosati.mumfordEulerDegree`
identifies the eventual squares in this criterion with ranks of actual
isogenies. Evaluation of the equality at `1` compares the Euler
characteristics of the tensor products with one copy of the ample
bundle, which are the restrictions of the corresponding exterior
tensor products to the endomorphism graphs.
