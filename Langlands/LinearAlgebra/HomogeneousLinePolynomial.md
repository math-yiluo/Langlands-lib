# A monic polynomial from a normalized binary homogeneous law

This internal algebraic construction is a prerequisite reduction for geometric
endomorphism degree polynomiality. It applies to every commutative semiring R
and does not assert any polynomial law for an abelian scheme.

`binaryLinePolynomial` sends a polynomial P in two variables to the ordinary
polynomial obtained by setting its second variable to one. The implementation
uses its finite monomial sum. Evaluation at x agrees with evaluation of P at
(x,1). When P is homogeneous of degree d, every supported exponent pair has
sum d, so the ordinary polynomial has degree at most d. Its coefficient at d
is exactly the value of P at (1,0). If that value is one and R is nontrivial,
the result is monic of degree d.

`exists_monic_linePolynomial` packages this construction for a function delta
on an R-module. It assumes that delta on the span of v,w is represented by a
binary homogeneous polynomial of degree d, and that delta(v)=1. It produces a
monic polynomial Q of degree d with Q(x)=delta(x*v+w). Every polynomiality
premise is explicit. In the intended future application v is the identity
endomorphism and w the negative of an endomorphism; proving that geometric
degree satisfies the premise is a separate, unproved geometric obligation.

Provenance is internal. The proof uses the standard finite monomial expansion,
the definition of homogeneous total degree and ordinary polynomial coefficient
and degree lemmas. It does not import or assume a Tate trace comparison.
