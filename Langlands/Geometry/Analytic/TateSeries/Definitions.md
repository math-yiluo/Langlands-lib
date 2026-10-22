# Monomials and continuous coefficient maps

Authors: Worker 36 (original construction), Worker 56 (coefficient generalization).

`monomial` is the actual finitely supported formal power series included in
`StrictTateAlgebra` using Mathlib's restrictedness proof. `coefficientCLM`
is coefficient extraction bundled as a continuous linear map; its bound
one follows from the coefficient supremum norm. Its value on a monomial is
the coefficient when the exponents agree and zero otherwise. Consequently
the monomial's Gauss norm is exactly the coefficient norm. These are the
intrinsic bounds and evaluation identities for the constructed maps.

The coefficient ring is any ultrametric normed commutative ring and the
variable type is arbitrary. Completeness is unnecessary for these maps.
Norm-convergent expansion is the separate proposition in `Statement.lean`;
this definitions module does not import or prove that proposition.

This is an internal coefficient interface for the restricted-series algebra
of the retained Berkovich-course notes, Section 2.1 p.1 and Section 2.2
pp.2-3, specialized to radius one. As in `TateAlgebra.md`, arbitrary variable
types and incomplete coefficient rings extend the source's finite-variable
Banach-algebra setting. The notes are undated notes of part of Vladimir
Berkovich's course, with unidentified note-taker.
Registered source: `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
